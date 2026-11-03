/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.VacuumBoozerTorus
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.ContinuousMap.Star

/-!
# Weighted Wirtinger bound for the Boozer spectrum on one invariant torus

Research note `notes/theory/dommaschk-qs-defect.md` (N-34), §2 relation (3) and module A2 of §6;
built on A1 `Theory/Fields/VacuumBoozerTorus`. Sources: Boozer, Phys. Fluids 24 (1981) 1999;
Helander, Rep. Prog. Phys. 77 (2014) 087001, §§3–4 (quasisymmetry in Boozer angles). The
oracle whose normalisation is formalised is `scripts/dommaschk_qa/fieldeval.py`
(`boozer_coeffs`, `qa_bad_modes`), `scripts/dommaschk_qa/diagnostics.py` and
`scripts/dommaschk_kam/qs_defect.py`.

## Setting (the KAM chart, no inverse angle map)

A torus is described on the chart `ℝ² ∋ p = (θ, φ)` by `v = V ∘ K` (vacuum: `Φ = φ + V`) and
`f = |B| ∘ K`, both doubly periodic with periods `2π` in `θ` and `2π/N` in `φ` (`N` field
periods; the oracle grid covers `[0, 2π) × [0, 2π/N)`, `N = NFP = 2`). Then (A1)
`θ_B = θ + ι v`, `φ_B = φ + v`, `J = 1 + v_φ + ι v_θ` (`chartJac`), and the QA defect
`g = ∂_{φ_B}|_{θ_B} f = (−ι v_φ f_θ + (1 + ι v_θ) f_φ)/J` (`chartDefect`; equal to
`torusQADefect` on a vacuum torus, `boozerJac_eq_chartJac_and_torusQADefect_eq`).

* `torusAvg N u = (2π · 2π/N)⁻¹ ∫∫_{[0,2π]×[0,2π/N]} u` (the oracle's grid mean);
* `boozerMode N ι v m n = exp(i (m θ_B − n N φ_B))`;
* **`boozerCoeff N ι v f m n = ⟨f J conj e_{mn}⟩ = ⟨f J e^{−i(mθ_B − nNφ_B)}⟩`** (the oracle's
  `c_mn`, `boozerCoeff_eq_oracle`); `boozerB00 = Re c_00 = ⟨f J⟩`;
* `weightedL2Sq N ι v g = ⟨g² J⟩` (`= ‖g‖²_{L²(J)}`; the oracle's `mean(g*g*J)/mean(J)`, with
  `⟨J⟩ = 1`);
* `OracleOffQA (m, n)`: the oracle's half lattice `n ≠ 0`, `m > 0` or (`m = 0`, `n > 0`);
  **`oracleDefect N ι v f S = sqrt(∑_{S} (2 |c_{mn}|)²)/B00`** (`A_mn = 2|c_mn|`).

## Results

* `integral_box_div`: the integral of a periodic divergence over a period box vanishes (Fubini
  and the fundamental theorem of calculus); `pθ_pφ` (symmetry of mixed partials).
* **`∂_{φ_B}` preserves `J dθ dφ`**: `integral_jacX` (`∫∫ J ∂_{φ_B} h = 0`: the divergence of
  `J e_{φ_B} = (−ι v_φ, 1 + ι v_θ)` vanishes; via `integral_bracket`), and `integral_jacY` for
  `∂_{θ_B}`; `integral_chartJac` (`⟨J⟩ = 1`).
* **Modes**: `jacX_boozerMode` (`∂_{φ_B} e_{mn} = −i n N e_{mn}`), `jacY_boozerMode`
  (`∂_{θ_B} e_{mn} = i m e_{mn}`), **orthonormality** `torusAvg_jac_boozerMode`
  (`⟨J e_{mn}⟩ = δ_{(m,n),0}`; no irrationality of `ι`, no change of variables).
* **Derivative identity** `boozerCoeff_chartDefect`: `c_{mn}(g) = −i n N c_{mn}(f)`.
* `bessel_finset`: Bessel's inequality for a positive `*`-functional; `weightedAvg`.
* **Main theorem** `BoozerChartHyp.sum_normSq_boozerCoeff_le`: for every finite `S` with
  `n ≠ 0`, `∑_{S} |c_{mn}(f)|² ≤ ⟨g² J⟩/N²`; full spectrum `tsum_normSq_boozerCoeff_le`.
* **Oracle normalisation**: `sum_oracle_le` (`∑_{S} A_{mn}² ≤ 2⟨g² J⟩/N²`),
  `sqrt_sum_oracle_le` (`defect · B00 ≤ (√2/N) ‖g‖_{L²(J)}`), `sqrt_sum_oracle_le_sup`
  (`≤ √2 δ/N = δ/√2` for `N = 2`), `le_boozerB00` (`B00 ≥ B_min`), `oracleDefect_le`
  (`defect ≤ √2 δ/(N B_min)`).
* **Concrete torus**: `BoozerChartHyp.of_torus`, `torus_tsum_normSq_boozerCoeff_le`,
  `torus_oracleDefect_le` (from `TorusQADefectLe B ι K δ` and `|B| ≥ B_min`).

## Sanity triad

* degenerate: `chartJac_zero`, `chartDefect_zero`, `boozerMode_zero_pot` (`v = 0`: `J = 1`,
  `g = ∂_φ f`, plain Fourier modes);
* QA: `boozerCoeff_eq_zero_of_defect_eq_zero` (`g ≡ 0` ⇒ no off-QA modes),
  `torus_oracleDefect_eq_zero_of_qa` (`|B| ∘ K = F ∘ θ_B` ⇒ oracle defect `0`);
* accepted/sharpness: `singleMode_bound_attained` (`f = b + cos Nφ`: defect `= 1/b =` the `L²`
  bound), `boozerCoeff_singleMode_ne_zero`; rejected: `not_oracleDefect_le_of_lt_sqrt_two`
  (no constant `c < √2` works).

**Hypotheses a concrete torus supplies** (`BoozerChartHyp`, or `BoozerChartHyp.of_torus`):
`V ∘ K` `C²` and `|B| ∘ K` `C¹` on `ℝ²`, both `(2π, 2π/N)`-periodic, `J > 0` (i.e. `B^φ > 0`).
**Not covered:** the identification of the KAM-grid mean with a field-line Birkhoff mean
(`fieldeval.boozer_coeffs`; equal for irrational `ι` by unique ergodicity).
-/

open scoped ComplexConjugate

public section
noncomputable section

namespace PlasmaLean.Fields.VacuumBoozer

open Real MeasureTheory Set Complex PlasmaLean.Contract

/-! ## Partial derivatives on the chart `ℝ²` and the divergence lemma -/

section Partials
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The partial derivative `∂_θ h` of a function on the chart `ℝ² ∋ (θ, φ)`. -/
@[expose] def pθ (h : ℝ × ℝ → E) (p : ℝ × ℝ) : E := fderiv ℝ h p (1, 0)

/-- The partial derivative `∂_φ h` of a function on the chart `ℝ² ∋ (θ, φ)`. -/
@[expose] def pφ (h : ℝ × ℝ → E) (p : ℝ × ℝ) : E := fderiv ℝ h p (0, 1)

/-- `∂_θ h` is the derivative of the section `t ↦ h (t, φ)`. -/
theorem hasDerivAt_pθ {h : ℝ × ℝ → E} {p : ℝ × ℝ} (hd : DifferentiableAt ℝ h p) :
    HasDerivAt (fun t => h (t, p.2)) (pθ h p) p.1 := by
  have hc : HasDerivAt (fun t : ℝ => (t, p.2)) ((1 : ℝ), (0 : ℝ)) p.1 :=
    (hasDerivAt_id' p.1).prodMk (hasDerivAt_const p.1 p.2)
  exact hd.hasFDerivAt.comp_hasDerivAt_of_eq p.1 hc rfl

/-- `∂_φ h` is the derivative of the section `t ↦ h (θ, t)`. -/
theorem hasDerivAt_pφ {h : ℝ × ℝ → E} {p : ℝ × ℝ} (hd : DifferentiableAt ℝ h p) :
    HasDerivAt (fun t => h (p.1, t)) (pφ h p) p.2 := by
  have hc : HasDerivAt (fun t : ℝ => (p.1, t)) ((0 : ℝ), (1 : ℝ)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id' p.2)
  exact hd.hasFDerivAt.comp_hasDerivAt_of_eq p.2 hc rfl

/-- The partials of a `C¹` function are continuous. -/
theorem continuous_pθ {h : ℝ × ℝ → E} (hh : ContDiff ℝ 1 h) : Continuous (pθ h) :=
  (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- The partials of a `C¹` function are continuous. -/
theorem continuous_pφ {h : ℝ × ℝ → E} (hh : ContDiff ℝ 1 h) : Continuous (pφ h) :=
  (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- The partials of a `C²` function are `C¹`. -/
theorem contDiff_pθ {h : ℝ × ℝ → E} (hh : ContDiff ℝ 2 h) : ContDiff ℝ 1 (pθ h) :=
  (hh.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

/-- The partials of a `C²` function are `C¹`. -/
theorem contDiff_pφ {h : ℝ × ℝ → E} (hh : ContDiff ℝ 2 h) : ContDiff ℝ 1 (pφ h) :=
  (hh.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

/-- **Symmetry of the mixed partials** of a `C²` function: `∂_θ ∂_φ h = ∂_φ ∂_θ h`. -/
theorem pθ_pφ {h : ℝ × ℝ → E} (hh : ContDiff ℝ 2 h) (p : ℝ × ℝ) :
    pθ (pφ h) p = pφ (pθ h) p := by
  have hd : Differentiable ℝ (fderiv ℝ h) :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have e : ∀ w u : ℝ × ℝ, fderiv ℝ (fun q => fderiv ℝ h q w) p u = fderiv ℝ (fderiv ℝ h) p u w := by
    intro w u
    rw [fderiv_clm_apply (hd p) (differentiableAt_const w)]
    simp
  change fderiv ℝ (fun q => fderiv ℝ h q (0, 1)) p (1, 0) =
    fderiv ℝ (fun q => fderiv ℝ h q (1, 0)) p (0, 1)
  rw [e, e]
  exact (hh.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

/-- The derivative of a function invariant under a translation is invariant. -/
theorem fderiv_periodic {h : ℝ × ℝ → E} {c : ℝ × ℝ} (hp : ∀ p, h (p + c) = h p)
    (p : ℝ × ℝ) : fderiv ℝ h (p + c) = fderiv ℝ h p := by
  have : (fun q => h (q + c)) = h := funext hp
  rw [← fderiv_comp_add_right, this]

end Partials

section Divergence
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- One-dimensional step: the integral over a period of the derivative of a periodic function
vanishes. -/
theorem integral_Icc_deriv_periodic {F F' : ℝ → E} {a : ℝ} (ha : 0 ≤ a)
    (hd : ∀ t, HasDerivAt F (F' t) t) (hc : Continuous F') (hp : F a = F 0) :
    ∫ t in Icc 0 a, F' t = 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      (hc.intervalIntegrable _ _), hp, sub_self]

/-- **The integral of a periodic divergence over a period box vanishes**: for `C¹` fields `P`,
`Q` on `ℝ²` with `P(a, φ) = P(0, φ)` and `Q(θ, b) = Q(θ, 0)`,
`∫∫_{[0,a]×[0,b]} (∂_θ P + ∂_φ Q) = 0` (Fubini and the fundamental theorem of calculus). -/
theorem integral_box_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {P Q : ℝ × ℝ → E}
    (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q) (hPp : ∀ φ, P (a, φ) = P (0, φ))
    (hQp : ∀ θ, Q (θ, b) = Q (θ, 0)) :
    ∫ p in Icc 0 a ×ˢ Icc 0 b, (pθ P p + pφ Q p) = 0 := by
  have hcomp : IsCompact (Icc (0:ℝ) a ×ˢ Icc (0:ℝ) b) := isCompact_Icc.prod isCompact_Icc
  rw [integral_add ((continuous_pθ hP).continuousOn.integrableOn_compact hcomp)
    ((continuous_pφ hQ).continuousOn.integrableOn_compact hcomp)]
  have h1 : ∫ p in Icc 0 a ×ˢ Icc 0 b, pθ P p = 0 := by
    rw [Measure.volume_eq_prod, ← setIntegral_prod_swap, setIntegral_prod]
    · refine (setIntegral_congr_fun measurableSet_Icc fun φ _ => ?_).trans (integral_zero _ _)
      exact integral_Icc_deriv_periodic (F := fun t => P (t, φ)) ha
        (fun t => hasDerivAt_pθ (p := (t, φ)) (hP.differentiable one_ne_zero _))
        ((continuous_pθ hP).comp (by fun_prop)) (hPp φ)
    · exact ((continuous_pθ hP).comp continuous_swap).continuousOn.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)
  have h2 : ∫ p in Icc 0 a ×ˢ Icc 0 b, pφ Q p = 0 := by
    rw [Measure.volume_eq_prod, setIntegral_prod]
    · refine (setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_).trans (integral_zero _ _)
      exact integral_Icc_deriv_periodic (F := fun t => Q (θ, t)) hb
        (fun t => hasDerivAt_pφ (p := (θ, t)) (hQ.differentiable one_ne_zero _))
        ((continuous_pφ hQ).comp (by fun_prop)) (hQp θ)
    · exact (continuous_pφ hQ).continuousOn.integrableOn_compact hcomp
  rw [h1, h2, add_zero]

end Divergence

/-! ## The torus, its average and periodic functions -/

/-- The toroidal period `2π/N` of an `N`-field-period torus (the oracle grid covers
`φ ∈ [0, 2π/N)`, `N = NFP`). -/
@[expose] def perPhi (N : ℕ) : ℝ := 2 * π / N

/-- The period box `[0, 2π] × [0, 2π/N]` of the chart `(θ, φ)`. -/
@[expose] def torusBox (N : ℕ) : Set (ℝ × ℝ) := Icc 0 (2 * π) ×ˢ Icc 0 (perPhi N)

/-- The area `2π · 2π/N` of the period box. -/
@[expose] def torusArea (N : ℕ) : ℝ := 2 * π * perPhi N

/-- The **torus average** `⟨u⟩ = (area)⁻¹ ∫∫_{box} u dθ dφ` (the mean over the oracle's uniform
`(θ, φ)` grid). -/
@[expose] def torusAvg (N : ℕ) (u : ℝ × ℝ → ℂ) : ℂ :=
  ((torusArea N : ℝ) : ℂ)⁻¹ * ∫ p in torusBox N, u p

/-- A function on the chart is **doubly periodic** with periods `2π` in `θ` and `2π/N` in `φ`. -/
structure TorusPeriodic {E : Type*} (N : ℕ) (h : ℝ × ℝ → E) : Prop where
  /-- `2π`-periodic in `θ`. -/
  theta : ∀ p : ℝ × ℝ, h (p + (2 * π, 0)) = h p
  /-- `2π/N`-periodic in `φ`. -/
  phi : ∀ p : ℝ × ℝ, h (p + (0, perPhi N)) = h p

/-- The toroidal period is positive. -/
theorem perPhi_pos {N : ℕ} (hN : 0 < N) : 0 < perPhi N := by
  unfold perPhi; positivity

/-- The area of the period box is positive. -/
theorem torusArea_pos {N : ℕ} (hN : 0 < N) : 0 < torusArea N := by
  unfold torusArea; have := perPhi_pos hN; positivity

/-- The period box is compact. -/
theorem isCompact_torusBox (N : ℕ) : IsCompact (torusBox N) := isCompact_Icc.prod isCompact_Icc

/-- The period box is measurable. -/
theorem measurableSet_torusBox (N : ℕ) : MeasurableSet (torusBox N) :=
  measurableSet_Icc.prod measurableSet_Icc

/-- Continuous functions are integrable on the period box. -/
theorem integrableOn_torusBox {N : ℕ} {E : Type*} [NormedAddCommGroup E] {u : ℝ × ℝ → E}
    (hu : Continuous u) : IntegrableOn u (torusBox N) :=
  hu.continuousOn.integrableOn_compact (isCompact_torusBox N)

/-- The volume of the period box is its area. -/
theorem integral_torusBox_one {N : ℕ} (hN : 0 < N) :
    ∫ _p in torusBox N, (1 : ℂ) = (torusArea N : ℂ) := by
  have h1 := (perPhi_pos hN).le
  rw [setIntegral_const, torusBox, Measure.volume_eq_prod, measureReal_def, Measure.prod_prod,
    Real.volume_Icc, Real.volume_Icc, sub_zero, sub_zero, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal two_pi_pos.le, torusArea]
  simp

section PeriodicIntegrals
variable {N : ℕ}

/-- `∫∫ ∂_θ h = 0` for a doubly periodic `C¹` function. -/
theorem integral_pθ_eq_zero (hN : 0 < N) {h : ℝ × ℝ → ℂ} (hh : ContDiff ℝ 1 h)
    (hp : TorusPeriodic N h) : ∫ p in torusBox N, pθ h p = 0 := by
  have := integral_box_div two_pi_pos.le (perPhi_pos hN).le hh (contDiff_const (c := (0 : ℂ)))
    (fun φ => by simpa using hp.theta (0, φ)) (fun _ => rfl)
  simpa [pφ, torusBox] using this

/-- `∫∫ ∂_φ h = 0` for a doubly periodic `C¹` function. -/
theorem integral_pφ_eq_zero (hN : 0 < N) {h : ℝ × ℝ → ℂ} (hh : ContDiff ℝ 1 h)
    (hp : TorusPeriodic N h) : ∫ p in torusBox N, pφ h p = 0 := by
  have := integral_box_div two_pi_pos.le (perPhi_pos hN).le (contDiff_const (c := (0 : ℂ))) hh
    (fun _ => rfl) (fun θ => by simpa using hp.phi (θ, 0))
  simpa [pθ, torusBox] using this

/-- The partials of a doubly periodic function are doubly periodic. -/
theorem TorusPeriodic.pθ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : ℝ × ℝ → E} (hp : TorusPeriodic N h) : TorusPeriodic N (pθ h) :=
  ⟨fun p => by simp only [VacuumBoozer.pθ, fderiv_periodic hp.theta],
    fun p => by simp only [VacuumBoozer.pθ, fderiv_periodic hp.phi]⟩

/-- The partials of a doubly periodic function are doubly periodic. -/
theorem TorusPeriodic.pφ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : ℝ × ℝ → E} (hp : TorusPeriodic N h) : TorusPeriodic N (pφ h) :=
  ⟨fun p => by simp only [VacuumBoozer.pφ, fderiv_periodic hp.theta],
    fun p => by simp only [VacuumBoozer.pφ, fderiv_periodic hp.phi]⟩

/-- Products of a real and a complex doubly periodic function are doubly periodic. -/
theorem TorusPeriodic.ofReal_mul {w : ℝ × ℝ → ℝ} {h : ℝ × ℝ → ℂ} (hw : TorusPeriodic N w)
    (hh : TorusPeriodic N h) : TorusPeriodic N (fun p => (w p : ℂ) * h p) :=
  ⟨fun p => by simp only [hw.theta p, hh.theta p], fun p => by simp only [hw.phi p, hh.phi p]⟩

/-- The derivative of `(w : ℂ) · h` (real `w`, complex `h`) in a direction `u`. -/
theorem fderiv_ofReal_mul_apply {w : ℝ × ℝ → ℝ} {h : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (hw : DifferentiableAt ℝ w p) (hh : DifferentiableAt ℝ h p) (u : ℝ × ℝ) :
    fderiv ℝ (fun q => (w q : ℂ) * h q) p u =
      (fderiv ℝ w p u : ℂ) * h p + (w p : ℂ) * fderiv ℝ h p u := by
  have hw' : HasFDerivAt (fun q => (w q : ℂ)) (ofRealCLM.comp (fderiv ℝ w p)) p :=
    ofRealCLM.hasFDerivAt.comp p hw.hasFDerivAt
  have := (hw'.mul hh.hasFDerivAt).fderiv
  rw [show (fun q => (w q : ℂ) * h q) = (fun q => (w q : ℂ)) * h from rfl, this]
  simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.comp_apply, ofRealCLM_apply, smul_eq_mul]
  ring

/-- **The bracket identity**: for `v` doubly periodic and `C²` and `h` doubly periodic and `C¹`,
`∫∫ (v_φ h_θ − v_θ h_φ) dθ dφ = 0` (it is the divergence of `(v_φ h, −v_θ h)`; the mixed
partials of `v` cancel). -/
theorem integral_bracket (hN : 0 < N) {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (hvp : TorusPeriodic N v) {h : ℝ × ℝ → ℂ} (hh : ContDiff ℝ 1 h) (hhp : TorusPeriodic N h) :
    ∫ p in torusBox N, (((pφ v p : ℝ) : ℂ) * pθ h p - ((pθ v p : ℝ) : ℂ) * pφ h p) = 0 := by
  have hv1 := contDiff_pφ hv
  have hv2 := contDiff_pθ hv
  have hnv : ContDiff ℝ 2 (fun p => -v p) := hv.neg
  have hv3 := contDiff_pθ hnv
  have hP : ContDiff ℝ 1 (fun p => ((pφ v p : ℝ) : ℂ) * h p) :=
    (ofRealCLM.contDiff.comp hv1).mul hh
  have hQ : ContDiff ℝ 1 (fun p => ((pθ (fun q => -v q) p : ℝ) : ℂ) * h p) :=
    (ofRealCLM.contDiff.comp hv3).mul hh
  have key := integral_box_div two_pi_pos.le (perPhi_pos hN).le hP hQ
    (fun φ => by simpa using (hvp.pφ.ofReal_mul hhp).theta (0, φ))
    (fun θ => by
      simpa using ((TorusPeriodic.pθ (N := N) (h := fun q => -v q) ⟨fun p => by simp [hvp.theta p],
        fun p => by simp [hvp.phi p]⟩).ofReal_mul hhp).phi (θ, 0))
  rw [← key]
  refine setIntegral_congr_fun (measurableSet_torusBox N) fun p _ => ?_
  have d1 := hv1.differentiable one_ne_zero p
  have d3 := hv3.differentiable one_ne_zero p
  have dh := hh.differentiable one_ne_zero p
  have e1 : pθ (fun q => ((pφ v q : ℝ) : ℂ) * h q) p =
      ((pθ (pφ v) p : ℝ) : ℂ) * h p + ((pφ v p : ℝ) : ℂ) * pθ h p :=
    fderiv_ofReal_mul_apply d1 dh (1, 0)
  have e2 : pφ (fun q => ((pθ (fun q => -v q) q : ℝ) : ℂ) * h q) p =
      ((pφ (pθ fun q => -v q) p : ℝ) : ℂ) * h p + ((pθ (fun q => -v q) p : ℝ) : ℂ) * pφ h p :=
    fderiv_ofReal_mul_apply d3 dh (0, 1)
  have hneg : pθ (fun q => -v q) = fun q => -pθ v q := by
    funext q; simp [VacuumBoozer.pθ]
  have hneg2 : pφ (fun q => -pθ v q) p = -pφ (pθ v) p := by
    simp [VacuumBoozer.pφ]
  rw [e1, e2, hneg, hneg2, ← pθ_pφ hv p]
  push_cast
  ring

end PeriodicIntegrals

/-! ## The vacuum Boozer angles in the chart, the defect and the invariance of `J dθ dφ` -/

section Chart
variable {N : ℕ} {ι : ℝ} {v : ℝ × ℝ → ℝ}

/-- The Boozer Jacobian in the chart, `J = 1 + v_φ + ι v_θ` (`v = V ∘ K`; equal to `boozerJac`
in vacuum by `boozerJac_eq_partials`). -/
@[expose] def chartJac (ι : ℝ) (v : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := 1 + pφ v p + ι * pθ v p

/-- The vacuum Boozer poloidal angle in the chart, `θ_B = θ + ι v`. -/
@[expose] def chartThetaB (ι : ℝ) (v : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := p.1 + ι * v p

/-- The vacuum Boozer toroidal angle in the chart, `φ_B = φ + v`. -/
@[expose] def chartPhiB (v : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := p.2 + v p

/-- The QA defect `g = ∂_{φ_B}|_{θ_B} f` in the chart: `boozerDeriv` with `a = v_θ`, `J`,
`f_θ` and `𝓛f = f_φ + ι f_θ` (on a vacuum torus this is `torusQADefect`, see
`torusQADefect_eq_chartDefect`). -/
@[expose] def chartDefect (ι : ℝ) (v f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  boozerDeriv ι (pθ v p) (chartJac ι v p) (pθ f p) (pφ f p + ι * pθ f p)

/-- `g J = −ι v_φ f_θ + (1 + ι v_θ) f_φ` (the chart form of `J ∂_{φ_B}`). -/
theorem chartDefect_mul_jac {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hJ : chartJac ι v p ≠ 0) :
    chartDefect ι v f p * chartJac ι v p =
      -(ι * pφ v p) * pθ f p + (1 + ι * pθ v p) * pφ f p := by
  rw [chartDefect, boozerDeriv_eq_chart]
  have e : chartJac ι v p - 1 - ι * pθ v p = pφ v p := by unfold chartJac; ring
  rw [e]
  field_simp

/-- The partial derivatives of a real function, complexified. -/
theorem fderiv_ofReal_apply {w : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hw : DifferentiableAt ℝ w p)
    (u : ℝ × ℝ) : fderiv ℝ (fun q => (w q : ℂ)) p u = (fderiv ℝ w p u : ℂ) := by
  have := (ofRealCLM.hasFDerivAt.comp p hw.hasFDerivAt).fderiv
  rw [show (fun q => (w q : ℂ)) = ofRealCLM ∘ w from rfl, this]
  rfl

/-- `J` is continuous for a `C²` potential. -/
theorem continuous_chartJac (hv : ContDiff ℝ 2 v) : Continuous (chartJac ι v) := by
  have h1 := continuous_pθ (hv.of_le (by norm_num))
  have h2 := continuous_pφ (hv.of_le (by norm_num))
  unfold chartJac; fun_prop

/-- **`∂_{φ_B}` preserves `J dθ dφ`**: for `v` doubly periodic and `C²` and `h` doubly periodic
and `C¹`, `∫∫ J ∂_{φ_B} h = ∫∫ (−ι v_φ h_θ + (1 + ι v_θ) h_φ) = 0` (note §2(3): the divergence
of `J e_{φ_B} = (−ι v_φ, 1 + ι v_θ)` vanishes). -/
theorem integral_jacX (hN : 0 < N) (hv : ContDiff ℝ 2 v) (hvp : TorusPeriodic N v)
    {h : ℝ × ℝ → ℂ} (hh : ContDiff ℝ 1 h) (hhp : TorusPeriodic N h) :
    ∫ p in torusBox N, (((-(ι * pφ v p) : ℝ) : ℂ) * pθ h p +
      (((1 + ι * pθ v p) : ℝ) : ℂ) * pφ h p) = 0 := by
  have a1 := continuous_pθ (hv.of_le (by norm_num))
  have a2 := continuous_pφ (hv.of_le (by norm_num))
  have b1 := continuous_pθ hh
  have b2 := continuous_pφ hh
  have hc : Continuous fun p => ((pφ v p : ℝ) : ℂ) * pθ h p - ((pθ v p : ℝ) : ℂ) * pφ h p := by
    fun_prop
  calc _ = ∫ p in torusBox N, (pφ h p - (ι : ℂ) *
        (((pφ v p : ℝ) : ℂ) * pθ h p - ((pθ v p : ℝ) : ℂ) * pφ h p)) :=
        setIntegral_congr_fun (measurableSet_torusBox N) fun p _ => by push_cast; ring
    _ = (∫ p in torusBox N, pφ h p) - (ι : ℂ) * ∫ p in torusBox N,
        (((pφ v p : ℝ) : ℂ) * pθ h p - ((pθ v p : ℝ) : ℂ) * pφ h p) := by
        rw [integral_sub (integrableOn_torusBox b2) ((integrableOn_torusBox hc).const_mul _),
          integral_const_mul]
    _ = 0 := by rw [integral_pφ_eq_zero hN hh hhp, integral_bracket hN hv hvp hh hhp]; ring

/-- **`∂_{θ_B}` preserves `J dθ dφ`**: `∫∫ ((1 + v_φ) h_θ − v_θ h_φ) = 0` (the divergence of
`J e_{θ_B} = (1 + v_φ, −v_θ)` vanishes). -/
theorem integral_jacY (hN : 0 < N) (hv : ContDiff ℝ 2 v) (hvp : TorusPeriodic N v)
    {h : ℝ × ℝ → ℂ} (hh : ContDiff ℝ 1 h) (hhp : TorusPeriodic N h) :
    ∫ p in torusBox N, ((((1 + pφ v p) : ℝ) : ℂ) * pθ h p - ((pθ v p : ℝ) : ℂ) * pφ h p) = 0 := by
  have a1 := continuous_pθ (hv.of_le (by norm_num))
  have a2 := continuous_pφ (hv.of_le (by norm_num))
  have b1 := continuous_pθ hh
  have b2 := continuous_pφ hh
  have hc : Continuous fun p => ((pφ v p : ℝ) : ℂ) * pθ h p - ((pθ v p : ℝ) : ℂ) * pφ h p := by
    fun_prop
  calc _ = ∫ p in torusBox N, (pθ h p +
        (((pφ v p : ℝ) : ℂ) * pθ h p - ((pθ v p : ℝ) : ℂ) * pφ h p)) :=
        setIntegral_congr_fun (measurableSet_torusBox N) fun p _ => by push_cast; ring
    _ = 0 := by
        rw [integral_add (integrableOn_torusBox b1) (integrableOn_torusBox hc),
          integral_pθ_eq_zero hN hh hhp, integral_bracket hN hv hvp hh hhp]; ring

/-- **The mean of the Jacobian is one**: `∫∫ J = area` (`v_θ`, `v_φ` have zero mean). -/
theorem integral_chartJac (hN : 0 < N) (hv : ContDiff ℝ 2 v) (hvp : TorusPeriodic N v) :
    ∫ p in torusBox N, ((chartJac ι v p : ℝ) : ℂ) = (torusArea N : ℂ) := by
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  have hc : ContDiff ℝ 1 (fun q => (v q : ℂ)) := ofRealCLM.contDiff.comp hv1
  have hcp : TorusPeriodic N (fun q => (v q : ℂ)) :=
    ⟨fun p => by simp [hvp.theta p], fun p => by simp [hvp.phi p]⟩
  have e1 : ∀ p, pθ (fun q => (v q : ℂ)) p = ((pθ v p : ℝ) : ℂ) := fun p =>
    fderiv_ofReal_apply (hv1.differentiable one_ne_zero p) _
  have e2 : ∀ p, pφ (fun q => (v q : ℂ)) p = ((pφ v p : ℝ) : ℂ) := fun p =>
    fderiv_ofReal_apply (hv1.differentiable one_ne_zero p) _
  have i1 := integral_pθ_eq_zero hN hc hcp
  have i2 := integral_pφ_eq_zero hN hc hcp
  simp only [e1, e2] at i1 i2
  have a1 := continuous_pθ hv1
  have a2 := continuous_pφ hv1
  have c1 : Continuous fun p => ((pθ v p : ℝ) : ℂ) := by fun_prop
  have c2 : Continuous fun p => ((pφ v p : ℝ) : ℂ) := by fun_prop
  calc _ = ∫ p in torusBox N, ((1 : ℂ) + ((pφ v p : ℝ) : ℂ) + (ι : ℂ) * ((pθ v p : ℝ) : ℂ)) :=
        setIntegral_congr_fun (measurableSet_torusBox N) fun p _ => by simp [chartJac]
    _ = (torusArea N : ℂ) := by
        rw [integral_add (integrableOn_torusBox (by fun_prop :
            Continuous fun p => (1 : ℂ) + ((pφ v p : ℝ) : ℂ)))
            ((integrableOn_torusBox c1).const_mul _),
          integral_add (integrableOn_torusBox continuous_const) (integrableOn_torusBox c2),
          integral_const_mul, i1, i2, integral_torusBox_one hN]
        ring

end Chart

/-! ## The Boozer modes -/

section Modes
variable {N : ℕ} {ι : ℝ} {v : ℝ × ℝ → ℝ}

/-- The Boozer phase `m θ_B − n N φ_B` of the mode `(m, n)` (`N` field periods). -/
@[expose] def boozerPhase (N : ℕ) (ι : ℝ) (v : ℝ × ℝ → ℝ) (m n : ℤ) (p : ℝ × ℝ) : ℝ :=
  m * chartThetaB ι v p - n * N * chartPhiB v p

/-- The **Boozer mode** `e_{mn} = exp(i (m θ_B − n N φ_B))`, as a function of the KAM chart
`(θ, φ)` (no inverse angle map is used). -/
@[expose] def boozerMode (N : ℕ) (ι : ℝ) (v : ℝ × ℝ → ℝ) (m n : ℤ) (p : ℝ × ℝ) : ℂ :=
  cexp ((boozerPhase N ι v m n p : ℂ) * I)

/-- The Boozer phase is as smooth as `v`. -/
theorem contDiff_boozerPhase {k : WithTop ℕ∞} (hv : ContDiff ℝ k v) (m n : ℤ) :
    ContDiff ℝ k (boozerPhase N ι v m n) := by
  unfold boozerPhase chartThetaB chartPhiB; fun_prop

/-- The Boozer modes are as smooth as `v`. -/
theorem contDiff_boozerMode {k : WithTop ℕ∞} (hv : ContDiff ℝ k v) (m n : ℤ) :
    ContDiff ℝ k (boozerMode N ι v m n) := by
  have := contDiff_boozerPhase (N := N) (ι := ι) hv m n
  have hc : ContDiff ℝ k (fun p => ((boozerPhase N ι v m n p : ℝ) : ℂ)) :=
    ofRealCLM.contDiff.comp this
  unfold boozerMode; fun_prop

/-- `|e_{mn}| = 1`. -/
theorem norm_boozerMode (m n : ℤ) (p : ℝ × ℝ) : ‖boozerMode N ι v m n p‖ = 1 :=
  norm_exp_ofReal_mul_I _

/-- `e_{mn} e_{pq} = e_{m+p, n+q}`. -/
theorem boozerMode_mul (m n m' n' : ℤ) (p : ℝ × ℝ) :
    boozerMode N ι v m n p * boozerMode N ι v m' n' p = boozerMode N ι v (m + m') (n + n') p := by
  unfold boozerMode boozerPhase
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- `conj e_{mn} = e_{−m, −n} = exp(−i (m θ_B − n N φ_B))`. -/
theorem conj_boozerMode (m n : ℤ) (p : ℝ × ℝ) :
    conj (boozerMode N ι v m n p) = boozerMode N ι v (-m) (-n) p := by
  unfold boozerMode boozerPhase
  rw [← Complex.exp_conj]; congr 1; simp only [map_mul, conj_ofReal, conj_I]; push_cast; ring

/-- `e_{00} = 1`. -/
theorem boozerMode_zero (p : ℝ × ℝ) : boozerMode N ι v 0 0 p = 1 := by
  simp [boozerMode, boozerPhase]

/-- The Boozer modes are doubly periodic (`θ_B` gains `2π` under `θ ↦ θ + 2π`, and `φ_B` gains
`2π/N` under `φ ↦ φ + 2π/N`, since `v` is doubly periodic). -/
theorem TorusPeriodic.boozerMode (hN : 0 < N) (hvp : TorusPeriodic N v) (m n : ℤ) :
    TorusPeriodic N (boozerMode N ι v m n) := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  constructor
  · intro p
    have e : (boozerPhase N ι v m n (p + (2 * π, 0)) : ℂ) * I =
        (boozerPhase N ι v m n p : ℂ) * I + (m : ℂ) * (2 * π * I) := by
      simp only [boozerPhase, chartThetaB, chartPhiB, hvp.theta p, Prod.fst_add, Prod.snd_add]
      push_cast; ring
    simp only [VacuumBoozer.boozerMode, e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
      mul_one]
  · intro p
    have e : (boozerPhase N ι v m n (p + (0, perPhi N)) : ℂ) * I =
        (boozerPhase N ι v m n p : ℂ) * I + ((-n : ℤ) : ℂ) * (2 * π * I) := by
      have hv' := hvp.phi p
      simp only [boozerPhase, chartThetaB, chartPhiB, hv', Prod.fst_add, Prod.snd_add]
      unfold perPhi
      have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
      push_cast; field_simp; ring
    simp only [VacuumBoozer.boozerMode, e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
      mul_one]

/-- The partials of the Boozer phase: `∂_θ(m θ_B − nN φ_B) = m (1 + ι v_θ) − nN v_θ`. -/
theorem pθ_boozerPhase (hv : ContDiff ℝ 1 v) (m n : ℤ) (p : ℝ × ℝ) :
    pθ (boozerPhase N ι v m n) p = m * (1 + ι * pθ v p) - n * N * pθ v p := by
  have hd := hasDerivAt_pθ (hv.differentiable one_ne_zero p)
  have h2 : HasDerivAt (fun t => boozerPhase N ι v m n (t, p.2))
      (m * (1 + ι * pθ v p) - n * N * pθ v p) p.1 := by
    have := (((hasDerivAt_id p.1).add (hd.const_mul ι)).const_mul (m : ℝ)).sub
      ((hd.const_add p.2).const_mul ((n : ℝ) * N))
    exact this
  exact (hasDerivAt_pθ ((contDiff_boozerPhase hv m n).differentiable one_ne_zero p)).unique h2

/-- `∂_φ(m θ_B − nN φ_B) = m ι v_φ − nN (1 + v_φ)`. -/
theorem pφ_boozerPhase (hv : ContDiff ℝ 1 v) (m n : ℤ) (p : ℝ × ℝ) :
    pφ (boozerPhase N ι v m n) p = m * (ι * pφ v p) - n * N * (1 + pφ v p) := by
  have hd := hasDerivAt_pφ (hv.differentiable one_ne_zero p)
  have h2 : HasDerivAt (fun t => boozerPhase N ι v m n (p.1, t))
      (m * (ι * pφ v p) - n * N * (1 + pφ v p)) p.2 := by
    have := ((hd.const_mul ι).const_add p.1 |>.const_mul (m : ℝ)).sub
      (((hasDerivAt_id p.2).add hd).const_mul ((n : ℝ) * N))
    exact this
  exact (hasDerivAt_pφ ((contDiff_boozerPhase hv m n).differentiable one_ne_zero p)).unique h2

/-- The derivative of a mode in a direction `u`: `D e = i e · D(phase)`. -/
theorem fderiv_boozerMode_apply (hv : ContDiff ℝ 1 v) (m n : ℤ) (p u : ℝ × ℝ) :
    fderiv ℝ (boozerMode N ι v m n) p u =
      boozerMode N ι v m n p * ((fderiv ℝ (boozerPhase N ι v m n) p u : ℂ) * I) := by
  have hd := (contDiff_boozerPhase (N := N) (ι := ι) hv m n).differentiable one_ne_zero p
  have h1 := ((ofRealCLM.hasFDerivAt.comp p hd.hasFDerivAt).mul_const I).cexp
  rw [show boozerMode N ι v m n =
    fun q => cexp ((ofRealCLM ∘ boozerPhase N ι v m n) q * I) from rfl, h1.fderiv]
  simp
  ring

/-- **`∂_{φ_B} e_{mn} = −i n N e_{mn}`** in the form `J ∂_{φ_B} e = −i n N J e`. -/
theorem jacX_boozerMode (hv : ContDiff ℝ 1 v) (m n : ℤ) (p : ℝ × ℝ) :
    ((-(ι * pφ v p) : ℝ) : ℂ) * pθ (boozerMode N ι v m n) p +
      (((1 + ι * pθ v p) : ℝ) : ℂ) * pφ (boozerMode N ι v m n) p =
      (-(n * N) * I) * (((chartJac ι v p : ℝ) : ℂ) * boozerMode N ι v m n p) := by
  have e1 : pθ (boozerMode N ι v m n) p =
      boozerMode N ι v m n p * (((pθ (boozerPhase N ι v m n) p : ℝ) : ℂ) * I) :=
    fderiv_boozerMode_apply hv m n p _
  have e2 : pφ (boozerMode N ι v m n) p =
      boozerMode N ι v m n p * (((pφ (boozerPhase N ι v m n) p : ℝ) : ℂ) * I) :=
    fderiv_boozerMode_apply hv m n p _
  rw [e1, e2, pθ_boozerPhase hv, pφ_boozerPhase hv, chartJac]
  push_cast; ring

/-- **`∂_{θ_B} e_{mn} = i m e_{mn}`** in the form `J ∂_{θ_B} e = i m J e`. -/
theorem jacY_boozerMode (hv : ContDiff ℝ 1 v) (m n : ℤ) (p : ℝ × ℝ) :
    (((1 + pφ v p) : ℝ) : ℂ) * pθ (boozerMode N ι v m n) p -
      ((pθ v p : ℝ) : ℂ) * pφ (boozerMode N ι v m n) p =
      ((m : ℂ) * I) * (((chartJac ι v p : ℝ) : ℂ) * boozerMode N ι v m n p) := by
  have e1 : pθ (boozerMode N ι v m n) p =
      boozerMode N ι v m n p * (((pθ (boozerPhase N ι v m n) p : ℝ) : ℂ) * I) :=
    fderiv_boozerMode_apply hv m n p _
  have e2 : pφ (boozerMode N ι v m n) p =
      boozerMode N ι v m n p * (((pφ (boozerPhase N ι v m n) p : ℝ) : ℂ) * I) :=
    fderiv_boozerMode_apply hv m n p _
  rw [e1, e2, pθ_boozerPhase hv, pφ_boozerPhase hv, chartJac]
  push_cast; ring

/-- **Orthogonality of the Boozer modes in `L²(J dθ dφ)`**: `∫∫ J e_{mn} = 0` for
`(m, n) ≠ (0, 0)` (from `integral_jacX` if `n ≠ 0`, from `integral_jacY` if `n = 0`, `m ≠ 0`;
no irrationality of `ι` and no change of variables is needed). -/
theorem integral_jac_boozerMode (hN : 0 < N) (hv : ContDiff ℝ 2 v) (hvp : TorusPeriodic N v)
    {m n : ℤ} (hmn : m ≠ 0 ∨ n ≠ 0) :
    ∫ p in torusBox N, ((chartJac ι v p : ℝ) : ℂ) * boozerMode N ι v m n p = 0 := by
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  have he := contDiff_boozerMode (N := N) (ι := ι) hv1 m n
  have hep := TorusPeriodic.boozerMode (ι := ι) hN hvp m n
  by_cases hn : n = 0
  · have hm : m ≠ 0 := hmn.resolve_right (not_not.2 hn)
    have h := integral_jacY hN hv hvp he hep
    simp only [jacY_boozerMode hv1, integral_const_mul] at h
    exact (mul_eq_zero.1 h).resolve_left (mul_ne_zero (by exact_mod_cast hm) I_ne_zero)
  · have h := integral_jacX (ι := ι) hN hv hvp he hep
    simp only [jacX_boozerMode hv1, integral_const_mul] at h
    refine (mul_eq_zero.1 h).resolve_left (mul_ne_zero ?_ I_ne_zero)
    have : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    exact neg_ne_zero.2 (mul_ne_zero (by exact_mod_cast hn) this)

end Modes

/-! ## Bessel's inequality for a positive functional -/

/-- **Bessel's inequality** for a positive `*`-linear functional `Λ` on a commutative
`*`-algebra (the form `⟨u, w⟩ = Λ(u w*)`): if the `e i` (`i ∈ s`) are orthonormal, then
`∑ |Λ(g e_i*)|² ≤ Re Λ(g g*)`. (Expand `Λ(r r*) ≥ 0` for `r = g − ∑ ⟨g, e_i⟩ e_i`.) -/
theorem bessel_finset {A : Type*} [CommRing A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (Λ : A →ₗ[ℂ] ℂ) (hstar : ∀ u, Λ (star u) = conj (Λ u))
    (hpos : ∀ u, 0 ≤ (Λ (u * star u)).re)
    {κ : Type*} [DecidableEq κ] (s : Finset κ) (e : κ → A)
    (horth : ∀ i ∈ s, ∀ j ∈ s, Λ (e i * star (e j)) = if i = j then 1 else 0) (g : A) :
    ∑ i ∈ s, ‖Λ (g * star (e i))‖ ^ 2 ≤ (Λ (g * star g)).re := by
  set c : κ → ℂ := fun i => Λ (g * star (e i)) with hc
  have hc' : ∀ i, Λ (e i * star g) = conj (c i) := fun i => by
    rw [hc, ← hstar, star_mul, star_star]
  set r := g - ∑ i ∈ s, c i • e i with hr
  have hsr : star r = star g - ∑ i ∈ s, conj (c i) • star (e i) := by
    simp [hr, star_sum, star_smul]
  have hdiag : ∀ x ∈ s, ∑ i ∈ s, conj (c x) * (c i * Λ (e i * star (e x))) =
      conj (c x) * c x := by
    intro x hx
    rw [Finset.sum_eq_single x (fun i hi hix => by simp [horth i hi x hx, hix])
      (fun h => absurd hx h)]
    simp [horth x hx x hx]
  have key : Λ (r * star r) = Λ (g * star g) - ∑ i ∈ s, c i * conj (c i) := by
    rw [hsr, hr]
    simp only [sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      map_sub, map_sum, map_smul, smul_eq_mul, hc']
    have h3 : ∑ x ∈ s, (conj (c x) * Λ (g * star (e x)) -
        ∑ i ∈ s, conj (c x) * (c i * Λ (e i * star (e x)))) = 0 :=
      Finset.sum_eq_zero fun x hx => by rw [hdiag x hx]; exact sub_self _
    rw [h3, sub_zero]
  have := hpos r
  rw [key, sub_re, re_sum] at this
  have e : ∀ i, (c i * conj (c i)).re = ‖c i‖ ^ 2 := fun i => by
    rw [mul_conj, normSq_eq_norm_sq, ofReal_re]
  simp only [e] at this
  linarith

/-! ## The `J`-weighted functional and the Boozer coefficients -/

section Coefficients
variable {N : ℕ} {ι : ℝ} {v : ℝ × ℝ → ℝ}

/-- The weighted average `u ↦ ⟨u w⟩` on continuous functions, as a `ℂ`-linear map (for the
weight `w = J` this is the `L²(J dθ dφ)` pairing `⟨u, e⟩ = ⟨u e* J⟩`). -/
@[expose] def weightedAvg (N : ℕ) (w : C(ℝ × ℝ, ℝ)) : C(ℝ × ℝ, ℂ) →ₗ[ℂ] ℂ where
  toFun u := torusAvg N (fun p => u p * (w p : ℂ))
  map_add' u u' := by
    have h1 : Continuous fun p => u p * (w p : ℂ) := by fun_prop
    have h2 : Continuous fun p => u' p * (w p : ℂ) := by fun_prop
    simp only [torusAvg, ContinuousMap.add_apply, add_mul]
    rw [integral_add (integrableOn_torusBox h1) (integrableOn_torusBox h2), mul_add]
  map_smul' c u := by
    simp only [torusAvg, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc,
      integral_const_mul]
    ring

/-- Unfolding `weightedAvg`. -/
theorem weightedAvg_apply (N : ℕ) (w : C(ℝ × ℝ, ℝ)) (u : C(ℝ × ℝ, ℂ)) :
    weightedAvg N w u = torusAvg N (fun p => u p * (w p : ℂ)) := rfl

/-- The weighted average commutes with conjugation (the weight is real). -/
theorem weightedAvg_star (N : ℕ) (w : C(ℝ × ℝ, ℝ)) (u : C(ℝ × ℝ, ℂ)) :
    weightedAvg N w (star u) = conj (weightedAvg N w u) := by
  simp only [weightedAvg_apply, torusAvg, ContinuousMap.star_apply, map_mul, map_inv₀,
    conj_ofReal]
  rw [← integral_conj]
  simp

/-- The weighted average is positive for a nonnegative weight. -/
theorem weightedAvg_mul_star_re_nonneg (N : ℕ) {w : C(ℝ × ℝ, ℝ)} (hw : ∀ p, 0 ≤ w p)
    (u : C(ℝ × ℝ, ℂ)) : 0 ≤ (weightedAvg N w (u * star u)).re := by
  have e : ∀ p, (u * star u) p * (w p : ℂ) = ((normSq (u p) * w p : ℝ) : ℂ) := fun p => by
    simp [mul_conj]
  simp only [weightedAvg_apply, torusAvg, e, integral_complex_ofReal]
  rw [← ofReal_inv, ← ofReal_mul, ofReal_re]
  refine mul_nonneg (inv_nonneg.2 ?_) (setIntegral_nonneg (measurableSet_torusBox N)
    fun p _ => mul_nonneg (normSq_nonneg _) (hw p))
  unfold torusArea perPhi; positivity

/-- The **Boozer Fourier coefficient** of `f` on the torus, in the KAM chart (the oracle's
`fieldeval.boozer_coeffs` / `qs_defect.py` formula):
`c_{mn}(f) = ⟨f J e^{−i (m θ_B − n N φ_B)}⟩`, the average over the period box of the chart
`(θ, φ)` with the Jacobian weight `J` and the conjugate Boozer mode. -/
@[expose] def boozerCoeff (N : ℕ) (ι : ℝ) (v f : ℝ × ℝ → ℝ) (m n : ℤ) : ℂ :=
  torusAvg N (fun p => ((f p * chartJac ι v p : ℝ) : ℂ) * conj (boozerMode N ι v m n p))

/-- The oracle's explicit form: `c_{mn}(f) = ⟨f J exp(−i (m θ_B − n N φ_B))⟩`. -/
theorem boozerCoeff_eq_oracle (N : ℕ) (ι : ℝ) (v f : ℝ × ℝ → ℝ) (m n : ℤ) :
    boozerCoeff N ι v f m n = torusAvg N (fun p => ((f p * chartJac ι v p : ℝ) : ℂ) *
      cexp (-((m * chartThetaB ι v p - n * N * chartPhiB v p : ℝ) : ℂ) * I)) := by
  unfold boozerCoeff boozerMode boozerPhase
  congr 1; funext p
  rw [← Complex.exp_conj]; congr 2
  simp only [map_mul, conj_ofReal, conj_I]; ring

/-- `c_{−m,−n}(f) = conj c_{mn}(f)` (`f` and `J` are real). -/
theorem boozerCoeff_neg (N : ℕ) (ι : ℝ) (v f : ℝ × ℝ → ℝ) (m n : ℤ) :
    boozerCoeff N ι v f (-m) (-n) = conj (boozerCoeff N ι v f m n) := by
  simp only [boozerCoeff, torusAvg, map_mul, map_inv₀, conj_ofReal]
  rw [← integral_conj]
  congr 2; funext p
  simp only [map_mul, conj_ofReal, conj_boozerMode, neg_neg]

/-- The weighted `L²(J)` mean square `⟨g² J⟩` (the oracle's `np.mean(g*g*J)/np.mean(J)`;
`⟨J⟩ = 1` by `integral_chartJac`). -/
@[expose] def weightedL2Sq (N : ℕ) (ι : ℝ) (v g : ℝ × ℝ → ℝ) : ℝ :=
  (torusArea N)⁻¹ * ∫ p in torusBox N, g p ^ 2 * chartJac ι v p

/-- **The derivative identity** `c_{mn}(∂_{φ_B} f) = −i n N c_{mn}(f)` (integration by parts
with `integral_jacX`: `∂_{φ_B}` preserves `J dθ dφ`, and `∂_{φ_B} e_{mn} = −i n N e_{mn}`). -/
theorem boozerCoeff_chartDefect (hN : 0 < N) (hv : ContDiff ℝ 2 v) (hvp : TorusPeriodic N v)
    {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hfp : TorusPeriodic N f)
    (hJ : ∀ p, chartJac ι v p ≠ 0) (m n : ℤ) :
    boozerCoeff N ι v (chartDefect ι v f) m n = (-(n * N) * I) * boozerCoeff N ι v f m n := by
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  set e := boozerMode N ι v (-m) (-n) with he_def
  have he := contDiff_boozerMode (N := N) (ι := ι) hv1 (-m) (-n)
  have hep := TorusPeriodic.boozerMode (ι := ι) hN hvp (-m) (-n)
  have hh : ContDiff ℝ 1 (fun p => (f p : ℂ) * e p) := (ofRealCLM.contDiff.comp hf).mul he
  have hhp : TorusPeriodic N (fun p => (f p : ℂ) * e p) := hfp.ofReal_mul hep
  have h := integral_jacX (ι := ι) hN hv hvp hh hhp
  have hpt : ∀ p, ((-(ι * pφ v p) : ℝ) : ℂ) * pθ (fun p => (f p : ℂ) * e p) p +
      (((1 + ι * pθ v p) : ℝ) : ℂ) * pφ (fun p => (f p : ℂ) * e p) p =
      ((chartDefect ι v f p * chartJac ι v p : ℝ) : ℂ) * e p +
        ((n * N : ℝ) * I) * (((f p * chartJac ι v p) : ℝ) * e p) := by
    intro p
    have d1 := hf.differentiable one_ne_zero p
    have d2 := he.differentiable one_ne_zero p
    have e1 : pθ (fun p => (f p : ℂ) * e p) p = ((pθ f p : ℝ) : ℂ) * e p + (f p : ℂ) * pθ e p :=
      fderiv_ofReal_mul_apply d1 d2 _
    have e2 : pφ (fun p => (f p : ℂ) * e p) p = ((pφ f p : ℝ) : ℂ) * e p + (f p : ℂ) * pφ e p :=
      fderiv_ofReal_mul_apply d1 d2 _
    have hX := jacX_boozerMode (N := N) (ι := ι) hv1 (-m) (-n) p
    rw [← he_def] at hX
    rw [e1, e2, chartDefect_mul_jac (hJ p)]
    push_cast at hX ⊢
    linear_combination (f p : ℂ) * hX
  simp only [hpt] at h
  have c1 : Continuous fun p => ((chartDefect ι v f p * chartJac ι v p : ℝ) : ℂ) * e p := by
    have hfun : (fun p => chartDefect ι v f p * chartJac ι v p) =
        fun p => -(ι * pφ v p) * pθ f p + (1 + ι * pθ v p) * pφ f p :=
      funext fun p => chartDefect_mul_jac (hJ p)
    have a1 := continuous_pθ hv1
    have a2 := continuous_pφ hv1
    have b1 := continuous_pθ hf
    have b2 := continuous_pφ hf
    have := he.continuous
    simp only [← he_def] at this
    have hc0 : Continuous fun p => chartDefect ι v f p * chartJac ι v p := by
      rw [hfun]; fun_prop
    fun_prop
  have c2 : Continuous fun p => (((f p * chartJac ι v p) : ℝ) : ℂ) * e p := by
    have := continuous_chartJac (ι := ι) hv
    have := he.continuous
    have := hf.continuous
    fun_prop
  rw [integral_add (integrableOn_torusBox c1) ((integrableOn_torusBox c2).const_mul _),
    integral_const_mul] at h
  have hc : ∀ g : ℝ × ℝ → ℝ, boozerCoeff N ι v g m n =
      ((torusArea N : ℝ) : ℂ)⁻¹ * ∫ p in torusBox N, ((g p * chartJac ι v p : ℝ) : ℂ) * e p := by
    intro g
    simp only [boozerCoeff, torusAvg, conj_boozerMode, he_def]
  rw [hc, hc, eq_neg_of_add_eq_zero_left h]
  push_cast; ring

end Coefficients

/-! ## The weighted Wirtinger bound for the off-QA Boozer spectrum -/

/-- **Hypotheses on one torus in the KAM chart** (`N` field periods): `v = V ∘ K` is `C²` and
`f = |B| ∘ K` is `C¹` on the chart `ℝ²`, both doubly periodic (periods `2π` in `θ`, `2π/N` in
`φ`), and the Boozer Jacobian `J = 1 + v_φ + ι v_θ` is positive. -/
structure BoozerChartHyp (N : ℕ) (ι : ℝ) (v f : ℝ × ℝ → ℝ) : Prop where
  /-- At least one field period. -/
  pos : 0 < N
  /-- `v = V ∘ K` is `C²` on the chart. -/
  v_smooth : ContDiff ℝ 2 v
  /-- `v` is doubly periodic. -/
  v_per : TorusPeriodic N v
  /-- `f = |B| ∘ K` is `C¹` on the chart. -/
  f_smooth : ContDiff ℝ 1 f
  /-- `f` is doubly periodic. -/
  f_per : TorusPeriodic N f
  /-- The Boozer Jacobian is positive. -/
  jac_pos : ∀ p, 0 < chartJac ι v p

section Wirtinger
variable {N : ℕ} {ι : ℝ} {v f : ℝ × ℝ → ℝ}

/-- **Orthonormality of the Boozer modes in `L²(J dθ dφ)`**:
`⟨J e_{mn}⟩ = 1` if `(m, n) = (0, 0)` and `0` otherwise. -/
theorem torusAvg_jac_boozerMode (hN : 0 < N) (hv : ContDiff ℝ 2 v) (hvp : TorusPeriodic N v)
    (m n : ℤ) :
    torusAvg N (fun p => ((chartJac ι v p : ℝ) : ℂ) * boozerMode N ι v m n p) =
      if m = 0 ∧ n = 0 then 1 else 0 := by
  have hA : ((torusArea N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (torusArea_pos hN).ne'
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp only [torusAvg, boozerMode_zero, mul_one, integral_chartJac hN hv hvp]
    exact inv_mul_cancel₀ hA
  · rw [not_and_or] at h
    simp only [torusAvg, integral_jac_boozerMode hN hv hvp h, mul_zero]

/-- The defect `g` is continuous. -/
theorem BoozerChartHyp.continuous_chartDefect (H : BoozerChartHyp N ι v f) :
    Continuous (chartDefect ι v f) := by
  have hv1 : ContDiff ℝ 1 v := H.v_smooth.of_le (by norm_num)
  have a1 := continuous_pθ hv1
  have a2 := continuous_pφ hv1
  have b1 := continuous_pθ H.f_smooth
  have b2 := continuous_pφ H.f_smooth
  have hJ := continuous_chartJac (ι := ι) H.v_smooth
  have : chartDefect ι v f = fun p =>
      (-(ι * pφ v p) * pθ f p + (1 + ι * pθ v p) * pφ f p) / chartJac ι v p := by
    funext p
    rw [← chartDefect_mul_jac (H.jac_pos p).ne', mul_div_cancel_right₀ _ (H.jac_pos p).ne']
  rw [this]
  exact Continuous.div (by fun_prop) hJ fun p => (H.jac_pos p).ne'

/-- **Bessel's inequality for the defect**: for every finite set `S` of modes,
`∑_{S} |c_{mn}(g)|² ≤ ⟨g² J⟩`. -/
theorem BoozerChartHyp.sum_normSq_coeff_defect_le (H : BoozerChartHyp N ι v f)
    (S : Finset (ℤ × ℤ)) :
    ∑ q ∈ S, ‖boozerCoeff N ι v (chartDefect ι v f) q.1 q.2‖ ^ 2 ≤
      weightedL2Sq N ι v (chartDefect ι v f) := by
  classical
  let w : C(ℝ × ℝ, ℝ) := ⟨chartJac ι v, continuous_chartJac H.v_smooth⟩
  let E : ℤ × ℤ → C(ℝ × ℝ, ℂ) := fun q =>
    ⟨boozerMode N ι v q.1 q.2, (contDiff_boozerMode H.v_smooth q.1 q.2).continuous⟩
  let G : C(ℝ × ℝ, ℂ) := ⟨fun p => (chartDefect ι v f p : ℂ),
    continuous_ofReal.comp H.continuous_chartDefect⟩
  have horth : ∀ i ∈ S, ∀ j ∈ S,
      weightedAvg N w (E i * star (E j)) = if i = j then 1 else 0 := by
    intro i _ j _
    have e : ∀ p, (E i * star (E j)) p * (w p : ℂ) =
        ((chartJac ι v p : ℝ) : ℂ) * boozerMode N ι v (i.1 - j.1) (i.2 - j.2) p := by
      intro p
      simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply, ContinuousMap.coe_mk, E, w,
        star_def, conj_boozerMode, boozerMode_mul, sub_eq_add_neg]
      ring
    rw [weightedAvg_apply]
    simp only [e]
    rw [torusAvg_jac_boozerMode H.pos H.v_smooth H.v_per]
    congr 1
    simp only [sub_eq_zero, Prod.ext_iff]
  have hB := bessel_finset (weightedAvg N w) (weightedAvg_star N w)
    (weightedAvg_mul_star_re_nonneg N (fun p => (H.jac_pos p).le)) S E horth G
  have e1 : ∀ q : ℤ × ℤ, weightedAvg N w (G * star (E q)) =
      boozerCoeff N ι v (chartDefect ι v f) q.1 q.2 := by
    intro q
    simp only [weightedAvg_apply, boozerCoeff, ContinuousMap.mul_apply, ContinuousMap.star_apply,
      ContinuousMap.coe_mk, E, G, w, star_def]
    congr 1; funext p; push_cast; ring
  have e2 : (weightedAvg N w (G * star G)).re = weightedL2Sq N ι v (chartDefect ι v f) := by
    have : ∀ p, (G * star G) p * (w p : ℂ) =
        ((chartDefect ι v f p ^ 2 * chartJac ι v p : ℝ) : ℂ) := by
      intro p
      simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply, ContinuousMap.coe_mk, G, w,
        star_def, conj_ofReal]
      push_cast; ring
    simp only [weightedAvg_apply, torusAvg, this, integral_complex_ofReal]
    rw [← ofReal_inv, ← ofReal_mul, ofReal_re, weightedL2Sq]
  simpa only [e1, e2] using hB

/-- **The weighted Wirtinger bound for the off-QA Boozer spectrum** (note N-34, §2(3)): for
every finite set `S` of modes `(m, n)` with `n ≠ 0`,
`∑_{(m,n) ∈ S} |c_{mn}(f)|² ≤ ⟨g² J⟩ / N²`, where `g = ∂_{φ_B} f` is the QA defect. The bound
is uniform in `S` (see `tsum_normSq_boozerCoeff_le` for the full spectrum). -/
theorem BoozerChartHyp.sum_normSq_boozerCoeff_le (H : BoozerChartHyp N ι v f)
    (S : Finset (ℤ × ℤ)) (hS : ∀ q ∈ S, q.2 ≠ 0) :
    ∑ q ∈ S, ‖boozerCoeff N ι v f q.1 q.2‖ ^ 2 ≤
      weightedL2Sq N ι v (chartDefect ι v f) / N ^ 2 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast H.pos
  have hc : ∀ q ∈ S, ‖boozerCoeff N ι v f q.1 q.2‖ ^ 2 ≤
      ‖boozerCoeff N ι v (chartDefect ι v f) q.1 q.2‖ ^ 2 / N ^ 2 := by
    intro q hq
    rw [boozerCoeff_chartDefect H.pos H.v_smooth H.v_per H.f_smooth H.f_per
      (fun p => (H.jac_pos p).ne'), norm_mul, mul_pow, le_div_iff₀ (by positivity)]
    have hn : (1 : ℝ) ≤ (q.2 : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ q.2 ^ 2 := by
        have := hS q hq
        nlinarith [sq_nonneg (q.2 - 1), sq_nonneg (q.2 + 1), Int.one_le_abs this, sq_abs q.2]
      exact_mod_cast this
    have e : ‖-((q.2 : ℂ) * N) * I‖ ^ 2 = (q.2 : ℝ) ^ 2 * N ^ 2 := by
      rw [norm_mul, norm_I, mul_one, norm_neg, norm_mul, mul_pow, Complex.norm_intCast,
        Complex.norm_natCast, sq_abs]
    rw [e]
    have := sq_nonneg ‖boozerCoeff N ι v f q.1 q.2‖
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hn) (sq_nonneg (N : ℝ))) this]
  calc _ ≤ ∑ q ∈ S, ‖boozerCoeff N ι v (chartDefect ι v f) q.1 q.2‖ ^ 2 / N ^ 2 :=
        Finset.sum_le_sum hc
    _ = (∑ q ∈ S, ‖boozerCoeff N ι v (chartDefect ι v f) q.1 q.2‖ ^ 2) / N ^ 2 :=
        (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right (H.sum_normSq_coeff_defect_le S) (by positivity)

/-- **The full off-QA spectrum**: `(m, n) ↦ |c_{mn}(f)|²` over `n ≠ 0` is summable and
`∑_{n ≠ 0} |c_{mn}(f)|² ≤ ⟨g² J⟩ / N²` (the supremum over finite sets of
`sum_normSq_boozerCoeff_le`; not only the oracle's truncation `m, |n| ≤ 8`). -/
theorem BoozerChartHyp.tsum_normSq_boozerCoeff_le (H : BoozerChartHyp N ι v f) :
    Summable (fun q : ℤ × ℤ => if q.2 ≠ 0 then ‖boozerCoeff N ι v f q.1 q.2‖ ^ 2 else 0) ∧
      ∑' q : ℤ × ℤ, (if q.2 ≠ 0 then ‖boozerCoeff N ι v f q.1 q.2‖ ^ 2 else 0) ≤
        weightedL2Sq N ι v (chartDefect ι v f) / N ^ 2 := by
  classical
  have hfin : ∀ S : Finset (ℤ × ℤ), ∑ q ∈ S,
      (if q.2 ≠ 0 then ‖boozerCoeff N ι v f q.1 q.2‖ ^ 2 else 0) ≤
        weightedL2Sq N ι v (chartDefect ι v f) / N ^ 2 := by
    intro S
    rw [← Finset.sum_filter]
    exact H.sum_normSq_boozerCoeff_le _ fun q hq => (Finset.mem_filter.1 hq).2
  have hnn : 0 ≤ fun q : ℤ × ℤ => if q.2 ≠ 0 then ‖boozerCoeff N ι v f q.1 q.2‖ ^ 2 else 0 :=
    fun q => by dsimp only; split_ifs <;> positivity
  refine ⟨summable_of_sum_le hnn hfin, tsum_le_of_sum_le' ?_ hfin⟩
  simpa using hfin ∅

/-- `⟨J⟩ = 1` (real form): `∫∫ J = area`. -/
theorem integral_chartJac_real (hN : 0 < N) (hv : ContDiff ℝ 2 v) (hvp : TorusPeriodic N v) :
    ∫ p in torusBox N, chartJac ι v p = torusArea N := by
  have := integral_chartJac (ι := ι) hN hv hvp
  rw [integral_complex_ofReal] at this
  exact_mod_cast this

/-- **`L²(J)` by sup**: if `|g| ≤ δ` then `⟨g² J⟩ ≤ δ²` (`J > 0`, `⟨J⟩ = 1`). -/
theorem BoozerChartHyp.weightedL2Sq_le (H : BoozerChartHyp N ι v f) {g : ℝ × ℝ → ℝ}
    (hg : Continuous g) {δ : ℝ} (hδ : ∀ p, |g p| ≤ δ) : weightedL2Sq N ι v g ≤ δ ^ 2 := by
  have hJc := continuous_chartJac (ι := ι) H.v_smooth
  have hA := torusArea_pos H.pos
  have hmono : ∫ p in torusBox N, g p ^ 2 * chartJac ι v p ≤
      ∫ p in torusBox N, δ ^ 2 * chartJac ι v p := by
    refine setIntegral_mono_on (integrableOn_torusBox (by fun_prop))
      (integrableOn_torusBox (by fun_prop)) (measurableSet_torusBox N) fun p _ => ?_
    have h1 : g p ^ 2 ≤ δ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hδ p) 2
    exact mul_le_mul_of_nonneg_right h1 (H.jac_pos p).le
  rw [integral_const_mul, integral_chartJac_real H.pos H.v_smooth H.v_per] at hmono
  unfold weightedL2Sq
  rw [inv_mul_le_iff₀ hA]
  linarith

/-- The `L²(J)` mean square is nonnegative. -/
theorem BoozerChartHyp.weightedL2Sq_nonneg (H : BoozerChartHyp N ι v f) (g : ℝ × ℝ → ℝ) :
    0 ≤ weightedL2Sq N ι v g :=
  mul_nonneg (inv_nonneg.2 (torusArea_pos H.pos).le) (setIntegral_nonneg
    (measurableSet_torusBox N) fun p _ => mul_nonneg (sq_nonneg _) (H.jac_pos p).le)

end Wirtinger

/-! ## The oracle-normalised defect -/

/-- The oracle's **half lattice of off-QA modes**: `n ≠ 0`, and `m > 0` or (`m = 0`, `n > 0`)
(`fieldeval.qa_bad_modes`, `qs_defect.py`: `m ≥ 0`, the `(0, n < 0)` modes are the conjugates
of `(0, −n)`). -/
@[expose] def OracleOffQA (q : ℤ × ℤ) : Prop := q.2 ≠ 0 ∧ (0 < q.1 ∨ (q.1 = 0 ∧ 0 < q.2))

/-- The oracle's `B00 = Re c_{00} = ⟨f J⟩`. -/
@[expose] def boozerB00 (N : ℕ) (ι : ℝ) (v f : ℝ × ℝ → ℝ) : ℝ := (boozerCoeff N ι v f 0 0).re

/-- The **oracle-normalised off-QA Boozer defect** over a finite set `S` of modes:
`sqrt(∑_{S} A_{mn}²)/B00` with the cosine amplitudes `A_{mn} = 2 |c_{mn}|`
(`diagnostics.py`, `qs_defect.py`: `defect = sqrt(Σ_{n≠0} A_mn²)/B00` over the half lattice). -/
@[expose] def oracleDefect (N : ℕ) (ι : ℝ) (v f : ℝ × ℝ → ℝ) (S : Finset (ℤ × ℤ)) : ℝ :=
  √(∑ q ∈ S, (2 * ‖boozerCoeff N ι v f q.1 q.2‖) ^ 2) / boozerB00 N ι v f

section Oracle
variable {N : ℕ} {ι : ℝ} {v f : ℝ × ℝ → ℝ}

/-- The half-lattice sum is twice the full-lattice sum:
`∑_{S} (2|c|)² ≤ 2 ⟨g² J⟩ / N²` for `S` in the oracle's half lattice (`S` and `−S` are
disjoint, and `|c_{−q}| = |c_q|`). -/
theorem BoozerChartHyp.sum_oracle_le (H : BoozerChartHyp N ι v f) (S : Finset (ℤ × ℤ))
    (hS : ∀ q ∈ S, OracleOffQA q) :
    ∑ q ∈ S, (2 * ‖boozerCoeff N ι v f q.1 q.2‖) ^ 2 ≤
      2 * (weightedL2Sq N ι v (chartDefect ι v f) / N ^ 2) := by
  classical
  set T := S.map (Equiv.neg (ℤ × ℤ)).toEmbedding
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro q hq hqT
    obtain ⟨q', hq', rfl⟩ := Finset.mem_map.1 hqT
    have h1 := (hS _ hq').2
    have h2 := (hS _ hq).2
    simp only [Equiv.toEmbedding_apply, Equiv.neg_apply, Prod.fst_neg, Prod.snd_neg] at h2
    omega
  have hT : ∑ q ∈ T, ‖boozerCoeff N ι v f q.1 q.2‖ ^ 2 =
      ∑ q ∈ S, ‖boozerCoeff N ι v f q.1 q.2‖ ^ 2 := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Equiv.toEmbedding_apply, Equiv.neg_apply, Prod.fst_neg, Prod.snd_neg,
      boozerCoeff_neg, Complex.norm_conj]
  have hU := H.sum_normSq_boozerCoeff_le (S ∪ T) (by
    intro q hq
    rcases Finset.mem_union.1 hq with h | h
    · exact (hS q h).1
    · obtain ⟨q', hq', rfl⟩ := Finset.mem_map.1 h
      simpa using (hS q' hq').1)
  rw [Finset.sum_union hdisj, hT] at hU
  calc _ = 4 * ∑ q ∈ S, ‖boozerCoeff N ι v f q.1 q.2‖ ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by ring
    _ ≤ _ := by linarith

/-- **The oracle-normalised bound, `L²` form** (note N-34, §2(3)):
`sqrt(∑_{S} A_{mn}²) ≤ (√2/N) ‖g‖_{L²(J)}` for every finite `S` in the half lattice, i.e.
`defect · B00 ≤ (√2/N) ‖g‖_{L²(J)}`. -/
theorem BoozerChartHyp.sqrt_sum_oracle_le (H : BoozerChartHyp N ι v f) (S : Finset (ℤ × ℤ))
    (hS : ∀ q ∈ S, OracleOffQA q) :
    √(∑ q ∈ S, (2 * ‖boozerCoeff N ι v f q.1 q.2‖) ^ 2) ≤
      √2 / N * √(weightedL2Sq N ι v (chartDefect ι v f)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast H.pos
  have h0 := H.weightedL2Sq_nonneg (chartDefect ι v f)
  calc _ ≤ √(2 * (weightedL2Sq N ι v (chartDefect ι v f) / N ^ 2)) :=
        Real.sqrt_le_sqrt (H.sum_oracle_le S hS)
    _ = _ := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_div' _ (by positivity),
          Real.sqrt_sq hN.le]
        ring

/-- **The oracle-normalised bound, sup form**: if `|g| ≤ δ` on the torus then
`sqrt(∑_{S} A_{mn}²) ≤ √2 δ / N` (`= δ/√2` for `N = 2`). -/
theorem BoozerChartHyp.sqrt_sum_oracle_le_sup (H : BoozerChartHyp N ι v f) (S : Finset (ℤ × ℤ))
    (hS : ∀ q ∈ S, OracleOffQA q) {δ : ℝ} (hδ : ∀ p, |chartDefect ι v f p| ≤ δ) :
    √(∑ q ∈ S, (2 * ‖boozerCoeff N ι v f q.1 q.2‖) ^ 2) ≤ √2 * δ / N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast H.pos
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ 0)
  have h1 := H.sqrt_sum_oracle_le S hS
  have h2 : √(weightedL2Sq N ι v (chartDefect ι v f)) ≤ δ := by
    rw [Real.sqrt_le_left hδ0]
    exact H.weightedL2Sq_le H.continuous_chartDefect hδ
  calc _ ≤ √2 / N * √(weightedL2Sq N ι v (chartDefect ι v f)) := h1
    _ ≤ √2 / N * δ := by gcongr
    _ = √2 * δ / N := by ring

/-- `B00 = ⟨f J⟩` (real form). -/
theorem boozerB00_eq (N : ℕ) (ι : ℝ) (v f : ℝ × ℝ → ℝ) :
    boozerB00 N ι v f = (torusArea N)⁻¹ * ∫ p in torusBox N, f p * chartJac ι v p := by
  simp only [boozerB00, boozerCoeff, torusAvg, boozerMode_zero, map_one, mul_one,
    integral_complex_ofReal]
  rw [← ofReal_inv, ← ofReal_mul, ofReal_re]

/-- `B00 ≥ B_min` if `f ≥ B_min` on the torus (`J > 0`, `⟨J⟩ = 1`). -/
theorem BoozerChartHyp.le_boozerB00 (H : BoozerChartHyp N ι v f) {Bmin : ℝ}
    (hB : ∀ p, Bmin ≤ f p) : Bmin ≤ boozerB00 N ι v f := by
  have hJc := continuous_chartJac (ι := ι) H.v_smooth
  have hf := H.f_smooth.continuous
  have hA := torusArea_pos H.pos
  have hmono : ∫ p in torusBox N, Bmin * chartJac ι v p ≤
      ∫ p in torusBox N, f p * chartJac ι v p :=
    setIntegral_mono_on (integrableOn_torusBox (by fun_prop))
      (integrableOn_torusBox (by fun_prop)) (measurableSet_torusBox N) fun p _ =>
        mul_le_mul_of_nonneg_right (hB p) (H.jac_pos p).le
  rw [integral_const_mul, integral_chartJac_real H.pos H.v_smooth H.v_per] at hmono
  rw [boozerB00_eq, le_inv_mul_iff₀ hA]
  linarith

/-- **The oracle-normalised defect bound** (note N-34, §2(3), `N` field periods): for every
finite set `S` of half-lattice off-QA modes, if `|∂_{φ_B}|B|| ≤ δ` and `|B| ≥ B_min > 0` on the
torus, then `defect ≤ √2 δ / (N B_min)` (`= δ/(√2 B_min)` for `N = 2`); and in `L²` form
`defect ≤ (√2/N) ‖g‖_{L²(J)} / B00`. -/
theorem BoozerChartHyp.oracleDefect_le (H : BoozerChartHyp N ι v f) (S : Finset (ℤ × ℤ))
    (hS : ∀ q ∈ S, OracleOffQA q) {δ Bmin : ℝ} (hδ : ∀ p, |chartDefect ι v f p| ≤ δ)
    (hBmin : 0 < Bmin) (hB : ∀ p, Bmin ≤ f p) :
    oracleDefect N ι v f S ≤
        √2 / N * √(weightedL2Sq N ι v (chartDefect ι v f)) / boozerB00 N ι v f ∧
      oracleDefect N ι v f S ≤ √2 * δ / (N * Bmin) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast H.pos
  have hB00 := H.le_boozerB00 hB
  have hpos : 0 < boozerB00 N ι v f := hBmin.trans_le hB00
  refine ⟨div_le_div_of_nonneg_right (H.sqrt_sum_oracle_le S hS) hpos.le, ?_⟩
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ 0)
  calc oracleDefect N ι v f S ≤ √2 * δ / N / boozerB00 N ι v f :=
        div_le_div_of_nonneg_right (H.sqrt_sum_oracle_le_sup S hS hδ) hpos.le
    _ ≤ √2 * δ / N / Bmin := div_le_div_of_nonneg_left (by positivity) hBmin hB00
    _ = √2 * δ / (N * Bmin) := by rw [div_div]

end Oracle

/-! ## The link to the torus quantities of `VacuumBoozerTorus` -/

section Torus
variable {B : Space → Space} {V : Space → ℝ} {R z : ℝ → ℝ → ℝ} {ι : ℝ}

/-- `v = V ∘ K` on the chart `ℝ² ∋ (θ, φ)`. -/
@[expose] def torusPot (V : Space → ℝ) (K : ℝ → ℝ → Space) (p : ℝ × ℝ) : ℝ := V (K p.1 p.2)

/-- `f = |B| ∘ K` on the chart `ℝ² ∋ (θ, φ)`. -/
@[expose] def torusModB (B : Space → Space) (K : ℝ → ℝ → Space) (p : ℝ × ℝ) : ℝ := ‖B (K p.1 p.2)‖

/-- **The chart quantities are the torus quantities** (vacuum): `boozerJac = J = 1 + v_φ + ι v_θ`
and `torusQADefect = chartDefect` (the defect `∂_{φ_B}|B|` of `VacuumBoozerTorus`), when
`v = V ∘ K` and `f = |B| ∘ K` are differentiable on the chart. -/
theorem boozerJac_eq_chartJac_and_torusQADefect_eq (hV : VacuumPotentialOn B V (cylTorus R z))
    (hR : ∀ θ φ, 0 < R θ φ) (hθ : ∀ θ φ, DifferentiableAt ℝ (fun t => cylTorus R z t φ) θ)
    (hL : ∀ θ φ, DifferentiableAt ℝ (fun t => cylTorus R z (θ + t * ι) (φ + t)) 0)
    (hv : Differentiable ℝ (torusPot V (cylTorus R z)))
    (hf : Differentiable ℝ (torusModB B (cylTorus R z))) (θ φ : ℝ) :
    boozerJac B ι (cylTorus R z) θ φ = chartJac ι (torusPot V (cylTorus R z)) (θ, φ) ∧
      torusQADefect B ι (cylTorus R z) θ φ =
        chartDefect ι (torusPot V (cylTorus R z)) (torusModB B (cylTorus R z)) (θ, φ) := by
  obtain ⟨ha, hJ⟩ := boozerJac_eq_partials hV (hv (θ, φ)).hasFDerivAt (hθ θ φ) (hL θ φ)
    (hR θ φ)
  have hJ' : boozerJac B ι (cylTorus R z) θ φ = chartJac ι (torusPot V (cylTorus R z)) (θ, φ) :=
    hJ
  refine ⟨hJ', ?_⟩
  have e1 : thetaDeriv (modB B (cylTorus R z)) θ φ = pθ (torusModB B (cylTorus R z)) (θ, φ) :=
    (hasDerivAt_pθ (p := (θ, φ)) (hf (θ, φ))).deriv
  have e2 : lineDeriv ι (modB B (cylTorus R z)) θ φ =
      pφ (torusModB B (cylTorus R z)) (θ, φ) + ι * pθ (torusModB B (cylTorus R z)) (θ, φ) := by
    have h := (hasDerivAt_line_of_hasFDerivAt (ι := ι) (hf (θ, φ)).hasFDerivAt).deriv
    rw [clm_apply_pair] at h
    simp only [lineDeriv]
    rw [show (fun t => modB B (cylTorus R z) (θ + t * ι) (φ + t)) =
      fun t => torusModB B (cylTorus R z) (θ + t * ι, φ + t) from rfl, h]
    simp only [pθ, pφ]; ring
  rw [torusQADefect, ha, hJ', e1, e2]
  rfl

/-- **The hypotheses of the Wirtinger bound for a concrete torus**: a `FieldTorus` of a vacuum
field with `v = V ∘ K` `C²`, `|B| ∘ K` `C¹`, both doubly periodic with `N` field periods, and
`J = B · 𝓛K > 0` (equivalently `B^φ > 0`, `boozerJac_pos_iff`). -/
theorem BoozerChartHyp.of_torus {N : ℕ} (hN : 0 < N) (hT : FieldTorus B R z ι)
    (hV : VacuumPotentialOn B V (cylTorus R z))
    (hθ : ∀ θ φ, DifferentiableAt ℝ (fun t => cylTorus R z t φ) θ)
    (hv : ContDiff ℝ 2 (torusPot V (cylTorus R z)))
    (hvp : TorusPeriodic N (torusPot V (cylTorus R z)))
    (hf : ContDiff ℝ 1 (torusModB B (cylTorus R z)))
    (hfp : TorusPeriodic N (torusModB B (cylTorus R z)))
    (hJ : ∀ θ φ, 0 < boozerJac B ι (cylTorus R z) θ φ) :
    BoozerChartHyp N ι (torusPot V (cylTorus R z)) (torusModB B (cylTorus R z)) where
  pos := hN
  v_smooth := hv
  v_per := hvp
  f_smooth := hf
  f_per := hfp
  jac_pos p := by
    rw [← (boozerJac_eq_chartJac_and_torusQADefect_eq hV hT.R_pos hθ hT.differentiableAt_line
      (hv.differentiable (by norm_num)) (hf.differentiable one_ne_zero) p.1 p.2).1]
    exact hJ p.1 p.2

/-- **The off-QA Boozer spectrum of a vacuum invariant torus** (`L²` form, full spectrum):
`∑_{n ≠ 0} |c_{mn}|² ≤ ⟨(∂_{φ_B}|B|)² J⟩ / N²`, with `∂_{φ_B}|B| = torusQADefect`. -/
theorem torus_tsum_normSq_boozerCoeff_le {N : ℕ} (hT : FieldTorus B R z ι)
    (hV : VacuumPotentialOn B V (cylTorus R z))
    (hθ : ∀ θ φ, DifferentiableAt ℝ (fun t => cylTorus R z t φ) θ)
    (H : BoozerChartHyp N ι (torusPot V (cylTorus R z)) (torusModB B (cylTorus R z))) :
    Summable (fun q : ℤ × ℤ => if q.2 ≠ 0 then
        ‖boozerCoeff N ι (torusPot V (cylTorus R z)) (torusModB B (cylTorus R z)) q.1 q.2‖ ^ 2
        else 0) ∧
      ∑' q : ℤ × ℤ, (if q.2 ≠ 0 then
        ‖boozerCoeff N ι (torusPot V (cylTorus R z)) (torusModB B (cylTorus R z)) q.1 q.2‖ ^ 2
        else 0) ≤
        weightedL2Sq N ι (torusPot V (cylTorus R z))
          (fun p => torusQADefect B ι (cylTorus R z) p.1 p.2) / N ^ 2 := by
  have e : (fun p : ℝ × ℝ => torusQADefect B ι (cylTorus R z) p.1 p.2) =
      chartDefect ι (torusPot V (cylTorus R z)) (torusModB B (cylTorus R z)) := funext fun p =>
    (boozerJac_eq_chartJac_and_torusQADefect_eq hV hT.R_pos hθ hT.differentiableAt_line
      (H.v_smooth.differentiable (by norm_num)) (H.f_smooth.differentiable one_ne_zero)
      p.1 p.2).2
  rw [e]
  exact H.tsum_normSq_boozerCoeff_le

/-- **The oracle-normalised Boozer defect of a vacuum invariant torus** (note N-34, §2(3)): if
`TorusQADefectLe B ι K δ` and `|B| ≥ B_min > 0` on the torus, then for every finite set `S` of
half-lattice off-QA modes, `defect = sqrt(∑_S A_{mn}²)/B00 ≤ √2 δ/(N B_min)`
(`= δ/(√2 B_min)` for `N = 2`), and `sqrt(∑_S A_{mn}²) ≤ √2 δ / N`. -/
theorem torus_oracleDefect_le {N : ℕ} (hT : FieldTorus B R z ι)
    (hV : VacuumPotentialOn B V (cylTorus R z))
    (hθ : ∀ θ φ, DifferentiableAt ℝ (fun t => cylTorus R z t φ) θ)
    (H : BoozerChartHyp N ι (torusPot V (cylTorus R z)) (torusModB B (cylTorus R z)))
    {δ Bmin : ℝ} (hδ : TorusQADefectLe B ι (cylTorus R z) δ) (hBmin : 0 < Bmin)
    (hB : ∀ θ φ, Bmin ≤ ‖B (cylTorus R z θ φ)‖) (S : Finset (ℤ × ℤ))
    (hS : ∀ q ∈ S, OracleOffQA q) :
    √(∑ q ∈ S, (2 * ‖boozerCoeff N ι (torusPot V (cylTorus R z)) (torusModB B (cylTorus R z))
        q.1 q.2‖) ^ 2) ≤ √2 * δ / N ∧
      oracleDefect N ι (torusPot V (cylTorus R z)) (torusModB B (cylTorus R z)) S ≤
        √2 * δ / (N * Bmin) := by
  have hδ' : ∀ p, |chartDefect ι (torusPot V (cylTorus R z)) (torusModB B (cylTorus R z)) p| ≤
      δ := fun p => by
    rw [← (boozerJac_eq_chartJac_and_torusQADefect_eq hV hT.R_pos hθ hT.differentiableAt_line
      (H.v_smooth.differentiable (by norm_num)) (H.f_smooth.differentiable one_ne_zero)
      p.1 p.2).2]
    exact hδ p.1 p.2
  exact ⟨H.sqrt_sum_oracle_le_sup S hS hδ',
    (H.oracleDefect_le S hS hδ' hBmin fun p => hB p.1 p.2).2⟩

end Torus

/-! ## Sanity checks -/

section Sanity
variable {N : ℕ} {ι : ℝ} {v f : ℝ × ℝ → ℝ}

/-- Linearity of the torus average on continuous functions. -/
theorem torusAvg_add {u w : ℝ × ℝ → ℂ} (hu : Continuous u) (hw : Continuous w) :
    torusAvg N (fun p => u p + w p) = torusAvg N u + torusAvg N w := by
  simp only [torusAvg]
  rw [integral_add (integrableOn_torusBox hu) (integrableOn_torusBox hw), mul_add]

/-- Homogeneity of the torus average. -/
theorem torusAvg_const_mul (c : ℂ) (u : ℝ × ℝ → ℂ) :
    torusAvg N (fun p => c * u p) = c * torusAvg N u := by
  simp only [torusAvg, integral_const_mul]; ring

/-- **Exact QA has no off-QA spectrum**: if the defect `g = ∂_{φ_B} f` vanishes identically,
then `c_{mn}(f) = 0` for every `n ≠ 0`. -/
theorem BoozerChartHyp.boozerCoeff_eq_zero_of_defect_eq_zero (H : BoozerChartHyp N ι v f)
    (hg : ∀ p, chartDefect ι v f p = 0) {m n : ℤ} (hn : n ≠ 0) : boozerCoeff N ι v f m n = 0 := by
  have h := boozerCoeff_chartDefect H.pos H.v_smooth H.v_per H.f_smooth H.f_per
    (fun p => (H.jac_pos p).ne') m n
  have h0 : boozerCoeff N ι v (chartDefect ι v f) m n = 0 := by
    simp [boozerCoeff, hg, torusAvg]
  rw [h0] at h
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast H.pos.ne'
  exact (mul_eq_zero.1 h.symm).resolve_left
    (mul_ne_zero (neg_ne_zero.2 (mul_ne_zero (by exact_mod_cast hn) hN)) I_ne_zero)

/-- **Exact QA on a vacuum torus**: if `|B| ∘ K = F ∘ θ_B` (`F` differentiable), the oracle
defect vanishes on every finite set of half-lattice off-QA modes (via
`torusQADefect_eq_zero_of_qa` and the sup bound with `δ = 0`). -/
theorem torus_oracleDefect_eq_zero_of_qa {B : Space → Space} {V : Space → ℝ}
    {R z : ℝ → ℝ → ℝ} (hT : FieldTorus B R z ι) (hV : VacuumPotentialOn B V (cylTorus R z))
    (hθ : ∀ θ φ, DifferentiableAt ℝ (fun t => cylTorus R z t φ) θ)
    (H : BoozerChartHyp N ι (torusPot V (cylTorus R z)) (torusModB B (cylTorus R z)))
    {F : ℝ → ℝ} (hQA : ∀ θ φ, ‖B (cylTorus R z θ φ)‖ = F (boozerThetaB ι V (cylTorus R z) θ φ))
    (hF : Differentiable ℝ F) {Bmin : ℝ} (hBmin : 0 < Bmin)
    (hB : ∀ θ φ, Bmin ≤ ‖B (cylTorus R z θ φ)‖) (S : Finset (ℤ × ℤ))
    (hS : ∀ q ∈ S, OracleOffQA q) :
    oracleDefect N ι (torusPot V (cylTorus R z)) (torusModB B (cylTorus R z)) S = 0 := by
  have h0 : TorusQADefectLe B ι (cylTorus R z) 0 := fun θ φ => by
    rw [torusQADefect_eq_zero_of_qa hT hV (hθ θ φ) hQA (hF _), abs_zero]
  have h := (torus_oracleDefect_le hT hV hθ H h0 hBmin hB S hS).2
  rw [mul_zero, zero_div] at h
  refine le_antisymm h (div_nonneg (Real.sqrt_nonneg _) ?_)
  exact hBmin.le.trans (H.le_boozerB00 fun p => hB p.1 p.2)

/-- Degenerate case `v = 0` (`B = ∇φ`-like angles): `J = 1`. -/
theorem chartJac_zero (ι : ℝ) (p : ℝ × ℝ) : chartJac ι (fun _ => 0) p = 1 := by
  simp [chartJac, pθ, pφ]

/-- Degenerate case `v = 0`: the defect is `∂_φ f` (`X = ∂_φ`). -/
theorem chartDefect_zero (ι : ℝ) (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    chartDefect ι (fun _ => 0) f p = pφ f p := by
  have h0 : pθ (fun _ : ℝ × ℝ => (0 : ℝ)) p = 0 := by simp [pθ]
  rw [chartDefect, chartJac_zero, h0, boozerDeriv_trivial]
  ring

/-- Degenerate case `v = 0`: the Boozer modes are the plain Fourier modes `e^{i(mθ − nNφ)}`. -/
theorem boozerMode_zero_pot (m n : ℤ) (p : ℝ × ℝ) :
    boozerMode N ι (fun _ => 0) m n p = cexp (((m * p.1 - n * N * p.2 : ℝ) : ℂ) * I) := by
  simp [boozerMode, boozerPhase, chartThetaB, chartPhiB]

/-- The single-mode test field `f = b + cos(N φ)` (with `v = 0`). -/
@[expose] def singleModeField (N : ℕ) (b : ℝ) (p : ℝ × ℝ) : ℝ := b + Real.cos (N * p.2)

/-- The single-mode test field is smooth. -/
theorem contDiff_singleModeField (N : ℕ) (b : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (singleModeField N b) := by
  unfold singleModeField; fun_prop

/-- The hypotheses hold for the single-mode test field. -/
theorem boozerChartHyp_singleMode (hN : 0 < N) (ι b : ℝ) :
    BoozerChartHyp N ι (fun _ => 0) (singleModeField N b) where
  pos := hN
  v_smooth := contDiff_const
  v_per := ⟨fun _ => rfl, fun _ => rfl⟩
  f_smooth := contDiff_singleModeField N b
  f_per := by
    have hN' : (N : ℝ) ≠ 0 := by positivity
    refine ⟨fun p => by simp [singleModeField], fun p => ?_⟩
    simp only [singleModeField, Prod.snd_add, perPhi]
    rw [show (N : ℝ) * (p.2 + 2 * π / N) = N * p.2 + 2 * π by field_simp, Real.cos_add_two_pi]
  jac_pos p := by rw [chartJac_zero]; exact one_pos

/-- `cos (k N φ) = (e_{0,k} + e_{0,−k})/2` for `v = 0`. -/
theorem ofReal_cos_eq_modes (k : ℤ) (p : ℝ × ℝ) :
    ((Real.cos (k * N * p.2) : ℝ) : ℂ) =
      (boozerMode N ι (fun _ => 0) 0 k p + boozerMode N ι (fun _ => 0) 0 (-k) p) / 2 := by
  rw [boozerMode_zero_pot, boozerMode_zero_pot, ofReal_cos, eq_div_iff two_ne_zero, mul_comm,
    two_cos]
  push_cast
  ring_nf

/-- For `v = 0`: `⟨e_{mn}⟩ = 1` if `(m, n) = (0, 0)` and `0` otherwise. -/
theorem torusAvg_boozerMode_zero_pot (hN : 0 < N) (m n : ℤ) :
    torusAvg N (boozerMode N ι (fun _ => 0) m n) = if m = 0 ∧ n = 0 then 1 else 0 := by
  rw [← torusAvg_jac_boozerMode (ι := ι) (v := fun _ => 0) hN contDiff_const
    ⟨fun _ => rfl, fun _ => rfl⟩ m n]
  refine congrArg (torusAvg N) (funext fun p => ?_)
  rw [chartJac_zero, ofReal_one, one_mul]

/-- The plain Fourier modes (`v = 0`) are continuous. -/
theorem continuous_boozerMode_zero_pot (m n : ℤ) :
    Continuous (boozerMode N ι (fun _ => 0) m n) :=
  (contDiff_boozerMode (k := 0) contDiff_const m n).continuous

/-- The single-mode coefficient: `c_{0,1}(b + cos Nφ) = 1/2`. -/
theorem boozerCoeff_singleMode_01 (hN : 0 < N) (ι b : ℝ) :
    boozerCoeff N ι (fun _ => 0) (singleModeField N b) 0 1 = 1 / 2 := by
  have e : ∀ p, ((singleModeField N b p * chartJac ι (fun _ => 0) p : ℝ) : ℂ) *
      conj (boozerMode N ι (fun _ => 0) 0 1 p) =
      (b : ℂ) * boozerMode N ι (fun _ => 0) 0 (-1) p +
        ((1 / 2 : ℂ) * boozerMode N ι (fun _ => 0) 0 0 p +
          (1 / 2 : ℂ) * boozerMode N ι (fun _ => 0) 0 (-2) p) := by
    intro p
    have hc := ofReal_cos_eq_modes (N := N) (ι := ι) 1 p
    have h1 := boozerMode_mul (N := N) (ι := ι) (v := fun _ => 0) 0 1 0 (-1) p
    have h2 := boozerMode_mul (N := N) (ι := ι) (v := fun _ => 0) 0 (-1) 0 (-1) p
    simp only [Int.cast_one, one_mul] at hc
    norm_num at h1 h2
    rw [conj_boozerMode, chartJac_zero, singleModeField, ofReal_mul, ofReal_add, hc, ofReal_one,
      mul_one, neg_zero]
    linear_combination (1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * h2
  rw [boozerCoeff]
  simp only [e]
  rw [torusAvg_add
      (by have := continuous_boozerMode_zero_pot (N := N) (ι := ι) 0 (-1); fun_prop) (by
      have := continuous_boozerMode_zero_pot (N := N) (ι := ι) 0 0
      have := continuous_boozerMode_zero_pot (N := N) (ι := ι) 0 (-2)
      fun_prop),
    torusAvg_add (by have := continuous_boozerMode_zero_pot (N := N) (ι := ι) 0 0; fun_prop)
      (by have := continuous_boozerMode_zero_pot (N := N) (ι := ι) 0 (-2); fun_prop),
    torusAvg_const_mul, torusAvg_const_mul, torusAvg_const_mul,
    torusAvg_boozerMode_zero_pot hN, torusAvg_boozerMode_zero_pot hN,
    torusAvg_boozerMode_zero_pot hN]
  norm_num

/-- The single-mode `B00 = b`. -/
theorem boozerB00_singleMode (hN : 0 < N) (ι b : ℝ) :
    boozerB00 N ι (fun _ => 0) (singleModeField N b) = b := by
  have e : ∀ p, ((singleModeField N b p * chartJac ι (fun _ => 0) p : ℝ) : ℂ) *
      conj (boozerMode N ι (fun _ => 0) 0 0 p) =
      (b : ℂ) * boozerMode N ι (fun _ => 0) 0 0 p +
        ((1 / 2 : ℂ) * boozerMode N ι (fun _ => 0) 0 1 p +
          (1 / 2 : ℂ) * boozerMode N ι (fun _ => 0) 0 (-1) p) := by
    intro p
    have hc := ofReal_cos_eq_modes (N := N) (ι := ι) 1 p
    simp only [Int.cast_one, one_mul] at hc
    rw [conj_boozerMode, chartJac_zero, singleModeField, ofReal_mul, ofReal_add, hc, ofReal_one,
      mul_one, neg_zero, boozerMode_zero]
    ring
  rw [boozerB00, boozerCoeff]
  simp only [e]
  rw [torusAvg_add (by have := continuous_boozerMode_zero_pot (N := N) (ι := ι) 0 0; fun_prop)
      (by
        have := continuous_boozerMode_zero_pot (N := N) (ι := ι) 0 1
        have := continuous_boozerMode_zero_pot (N := N) (ι := ι) 0 (-1)
        fun_prop),
    torusAvg_add (by have := continuous_boozerMode_zero_pot (N := N) (ι := ι) 0 1; fun_prop)
      (by have := continuous_boozerMode_zero_pot (N := N) (ι := ι) 0 (-1); fun_prop),
    torusAvg_const_mul, torusAvg_const_mul, torusAvg_const_mul,
    torusAvg_boozerMode_zero_pot hN, torusAvg_boozerMode_zero_pot hN,
    torusAvg_boozerMode_zero_pot hN]
  norm_num

/-- The single-mode defect: `g = ∂_φ (b + cos Nφ) = −N sin(Nφ)`. -/
theorem chartDefect_singleMode (ι b : ℝ) (p : ℝ × ℝ) :
    chartDefect ι (fun _ => 0) (singleModeField N b) p = -(N * Real.sin (N * p.2)) := by
  rw [chartDefect_zero]
  have h1 := hasDerivAt_pφ (p := p) ((contDiff_singleModeField (k := 1) N b).differentiable
    one_ne_zero p)
  have h2 : HasDerivAt (fun t => singleModeField N b (p.1, t)) (-(N * Real.sin (N * p.2))) p.2 :=
    (((hasDerivAt_id p.2).const_mul (N : ℝ)).cos.const_add b).congr_deriv (by
      simp only [id, mul_one]; ring)
  exact h1.unique h2

/-- The single-mode `⟨g² J⟩ = N²/2`. -/
theorem weightedL2Sq_singleMode (hN : 0 < N) (ι b : ℝ) :
    weightedL2Sq N ι (fun _ => 0) (chartDefect ι (fun _ => 0) (singleModeField N b)) =
      (N : ℝ) ^ 2 / 2 := by
  have e : ∀ p, (((chartDefect ι (fun _ => 0) (singleModeField N b) p) ^ 2 *
      chartJac ι (fun _ => 0) p : ℝ) : ℂ) =
      ((N : ℂ) ^ 2 / 2) * boozerMode N ι (fun _ => 0) 0 0 p +
        ((-(N : ℂ) ^ 2 / 4) * boozerMode N ι (fun _ => 0) 0 2 p +
          (-(N : ℂ) ^ 2 / 4) * boozerMode N ι (fun _ => 0) 0 (-2) p) := by
    intro p
    have hc := ofReal_cos_eq_modes (N := N) (ι := ι) 2 p
    have hs : Real.sin (N * p.2) ^ 2 = 1 / 2 - Real.cos (2 * N * p.2) / 2 := by
      have := Real.cos_two_mul (N * p.2)
      have := Real.sin_sq_add_cos_sq (N * p.2)
      rw [show 2 * (N : ℝ) * p.2 = 2 * (N * p.2) by ring]
      linarith
    rw [chartDefect_singleMode, chartJac_zero, boozerMode_zero]
    push_cast at hc ⊢
    rw [mul_one, neg_sq, mul_pow]
    have hs' := congrArg (fun x : ℝ => (x : ℂ)) hs
    push_cast at hs'
    rw [hs', hc]
    ring
  have hA : (((weightedL2Sq N ι (fun _ => 0) (chartDefect ι (fun _ => 0)
      (singleModeField N b))) : ℝ) : ℂ) =
      torusAvg N (fun p => (((chartDefect ι (fun _ => 0) (singleModeField N b) p) ^ 2 *
        chartJac ι (fun _ => 0) p : ℝ) : ℂ)) := by
    simp only [weightedL2Sq, torusAvg, integral_complex_ofReal]
    push_cast; ring
  simp only [e] at hA
  rw [torusAvg_add (by have := continuous_boozerMode_zero_pot (N := N) (ι := ι) 0 0; fun_prop)
      (by
        have := continuous_boozerMode_zero_pot (N := N) (ι := ι) 0 2
        have := continuous_boozerMode_zero_pot (N := N) (ι := ι) 0 (-2)
        fun_prop),
    torusAvg_add (by have := continuous_boozerMode_zero_pot (N := N) (ι := ι) 0 2; fun_prop)
      (by have := continuous_boozerMode_zero_pot (N := N) (ι := ι) 0 (-2); fun_prop),
    torusAvg_const_mul, torusAvg_const_mul, torusAvg_const_mul,
    torusAvg_boozerMode_zero_pot hN, torusAvg_boozerMode_zero_pot hN,
    torusAvg_boozerMode_zero_pot hN] at hA
  norm_num at hA
  apply ofReal_injective
  rw [hA]
  push_cast; ring

/-- **The bound is attained** (accepted fixture): for `f = b + cos(Nφ)`, `v = 0`, `b > 0`, the
oracle defect over `{(0, 1)}` is `1/b`, and so is the `L²` bound
`(√2/N) ‖g‖_{L²(J)} / B00`; the constant `√2/N` is sharp. -/
theorem singleMode_bound_attained (hN : 0 < N) (ι : ℝ) {b : ℝ} (hb : 0 < b) :
    oracleDefect N ι (fun _ => 0) (singleModeField N b) {(0, 1)} = 1 / b ∧
      √2 / N * √(weightedL2Sq N ι (fun _ => 0) (chartDefect ι (fun _ => 0)
        (singleModeField N b))) / boozerB00 N ι (fun _ => 0) (singleModeField N b) = 1 / b := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨?_, ?_⟩
  · rw [oracleDefect, Finset.sum_singleton, boozerCoeff_singleMode_01 hN, boozerB00_singleMode hN]
    norm_num
  · rw [weightedL2Sq_singleMode hN, boozerB00_singleMode hN, Real.sqrt_div' _ (by norm_num),
      Real.sqrt_sq hN'.le]
    have h2 : (0 : ℝ) < √2 := by positivity
    field_simp

/-- **Rejected fixture**: no constant `c < √2` can replace `√2` in the `L²` bound (the
single-mode field violates it). -/
theorem not_oracleDefect_le_of_lt_sqrt_two (hN : 0 < N) (ι : ℝ) {b c : ℝ} (hb : 0 < b)
    (hc : c < √2) :
    ¬ oracleDefect N ι (fun _ => 0) (singleModeField N b) {(0, 1)} ≤
      c / N * √(weightedL2Sq N ι (fun _ => 0) (chartDefect ι (fun _ => 0)
        (singleModeField N b))) / boozerB00 N ι (fun _ => 0) (singleModeField N b) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [(singleMode_bound_attained hN ι hb).1, weightedL2Sq_singleMode hN, boozerB00_singleMode hN,
    Real.sqrt_div' _ (by norm_num), Real.sqrt_sq hN'.le]
  have h2 : (0 : ℝ) < √2 := by positivity
  intro h
  have : c / N * (N / √2) / b = c / √2 / b := by field_simp
  rw [this, div_le_div_iff_of_pos_right hb, le_div_iff₀ h2] at h
  linarith

/-- The single-mode field is not QA: its `(0, 1)` coefficient is nonzero. -/
theorem boozerCoeff_singleMode_ne_zero (hN : 0 < N) (ι b : ℝ) :
    boozerCoeff N ι (fun _ => 0) (singleModeField N b) 0 1 ≠ 0 := by
  rw [boozerCoeff_singleMode_01 hN]; norm_num

end Sanity

end PlasmaLean.Fields.VacuumBoozer
