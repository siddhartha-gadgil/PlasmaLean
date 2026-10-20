/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.BoozerGuidingCentre
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Second-order near-axis quasi-axisymmetric model and alpha confinement (rung M4)

**Model status.** The field strength below is a truncated second-order near-axis expansion
(Garren–Boozer 1991; Landreman–Sengupta, JPP 85 (2019) 815850601) fitted to the pyQSC
"precise QA" configuration (Landreman–Paul, PRL 128 (2022) 035001):

    B(ψ, θ, φ) = B₀ (1 + η r cos θ) + r² (b₀ + b₁ cos 2φ) + B₂c r² cos 2θ,    r = √(2ψ/B₀),

with Boozer angles `θ, φ` and QA helicity `(N, M) = (0, 1)` (`ξ = ∂_φ`). It agrees with the
field strength of a real vacuum field near the precise-QA axis **only to the order of the
near-axis expansion** (formal asymptotics); the `O(r³)` remainder has no rigorous bound and
convergence of the near-axis series is open. All theorems here are about the model, inserted
into the vacuum Boozer guiding-centre model of `Theory/Kinetic/BoozerGuidingCentre`, whose
derivation from the Lorentz force is itself not formalized. The coefficients are rational
roundings (see `notes/theory/near-axis-quasisymmetry.md` §5).

Results:

* `nearAxis_symmetryDefect`: `ξB = −2 b₁ r² sin 2φ` exactly; `nearAxis_epsQS`: the symmetry
  defect on the surface of radius `r` has supremum `ε_QS(r) = 2|b₁| r²` (attained);
* `nearAxis_abs_sub_le`: `|B − B₀| ≤ B₀|η| r_c + r_c² (|b₀| + |b₁| + |B₂c|)` for `r ≤ r_c`;
* `preciseQA_epsQS`: normalized precise-QA fit, `ε_QS(r) = (7/500) r²`;
* `reactorQA`: the same model scaled to `a = 1.7 m`, `B₀ = 5.7 T` (length scale ≈ 9.59);
  `reactorQA_epsQS_edge`: `ε_QS(a) = 0.0024854 T`;
* `alpha_trapped_reactorQA`: every 3.5 MeV alpha guiding-centre orbit of the model with
  `|v_∥/v| ≥ 0.9`, starting at `r ≤ a/4`, stays at `ψ ≤ 8.2 T m²` (so `r < a`) for
  `0 ≤ t ≤ 8 × 10⁻⁴ s`.

**Honest assessment.** `0.8 ms` is roughly 500 times shorter than the alpha slowing-down
time (≈ 0.4 s). The cause is the linear-in-ε drift bound `|ΔP| ≤ (2H/B_min) ε t`: it treats the
defect `ξB = −2b₁ r² sin 2φ` as a constant-sign worst-case forcing, while along a passing orbit
`φ` advances monotonically and the defect averages out at leading order. Reaching 0.4 s with
this bound would need `ε_QS ≲ 10⁻⁶ B₀`; closing the gap needs an averaging lemma
(`T ∝ 1/ε²`), not a better field. Orbits are supplied; orbits through the magnetic axis are
outside the `(ψ, θ)` chart and not covered.
-/
public section
noncomputable section
namespace PlasmaLean.Design.NearAxisQA
open PlasmaLean.Kinetic.Boozer Real

/-- Near-axis radius `r = √(2ψ/B₀)` (with `ψ = B₀ r²/2`). -/
@[expose] def radius (B₀ ψ : ℝ) : ℝ := √(2 * ψ / B₀)

/-- `r² = 2ψ/B₀` for `ψ ≥ 0`, `B₀ > 0`. -/
theorem radius_sq {B₀ ψ : ℝ} (hB₀ : 0 < B₀) (hψ : 0 ≤ ψ) : radius B₀ ψ ^ 2 = 2 * ψ / B₀ :=
  sq_sqrt (by positivity)

/-- Second-order near-axis QA field strength, written with `r² = 2ψ/B₀`. -/
@[expose] def nearAxisB (B₀ η b₀ b₁ B₂c ψ θ φ : ℝ) : ℝ :=
  B₀ + B₀ * η * radius B₀ ψ * cos θ + 2 * ψ / B₀ * (b₀ + b₁ * cos (2 * φ) + B₂c * cos (2 * θ))

/-- `∂B/∂ψ`. -/
@[expose] def nearAxisBψ (B₀ η b₀ b₁ B₂c ψ θ φ : ℝ) : ℝ :=
  η * cos θ / radius B₀ ψ + 2 / B₀ * (b₀ + b₁ * cos (2 * φ) + B₂c * cos (2 * θ))

/-- `∂B/∂θ`. -/
@[expose] def nearAxisBθ (B₀ η B₂c ψ θ : ℝ) : ℝ :=
  -(B₀ * η * radius B₀ ψ * sin θ) - 2 * ψ / B₀ * (2 * B₂c * sin (2 * θ))

/-- `∂B/∂φ`. -/
@[expose] def nearAxisBφ (B₀ b₁ ψ φ : ℝ) : ℝ := -(2 * ψ / B₀ * (2 * b₁ * sin (2 * φ)))

/-- The near-axis field equals `B₀(1 + η r cos θ) + r²(b₀ + b₁ cos 2φ) + B₂c r² cos 2θ`. -/
theorem nearAxisB_eq {B₀ η b₀ b₁ B₂c ψ θ φ : ℝ} (hB₀ : 0 < B₀) (hψ : 0 ≤ ψ) :
    nearAxisB B₀ η b₀ b₁ B₂c ψ θ φ = B₀ * (1 + η * radius B₀ ψ * cos θ) +
      radius B₀ ψ ^ 2 * (b₀ + b₁ * cos (2 * φ)) + B₂c * radius B₀ ψ ^ 2 * cos (2 * θ) := by
  rw [radius_sq hB₀ hψ, nearAxisB]; ring

/-- Differentiability of the near-axis field on `ψ > 0` with the stated partials. -/
theorem nearAxisB_hasFDerivAt {B₀ η b₀ b₁ B₂c : ℝ} (hB₀ : 0 < B₀) (p : ℝ × ℝ × ℝ)
    (hp : 0 < p.1) :
    HasFDerivAt (fun p : ℝ × ℝ × ℝ => nearAxisB B₀ η b₀ b₁ B₂c p.1 p.2.1 p.2.2)
      (gradCLM (nearAxisBψ B₀ η b₀ b₁ B₂c p.1 p.2.1 p.2.2) (nearAxisBθ B₀ η B₂c p.1 p.2.1)
        (nearAxisBφ B₀ b₁ p.1 p.2.2)) p := by
  have hx : HasFDerivAt (fun p : ℝ × ℝ × ℝ => p.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    hasFDerivAt_fst
  have hy : HasFDerivAt (fun p : ℝ × ℝ × ℝ => p.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    hasFDerivAt_snd.fst
  have hz : HasFDerivAt (fun p : ℝ × ℝ × ℝ => p.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    hasFDerivAt_snd.snd
  have harg : 2 * p.1 / B₀ ≠ 0 := by positivity
  have h2 : HasFDerivAt (fun y : ℝ × ℝ × ℝ => 2 * y.1 / B₀)
      ((2 / B₀) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p := by
    convert hx.const_mul (2 / B₀) using 1; funext y; ring
  have hr := h2.sqrt harg
  have hrpos : 0 < √(2 * p.1 / B₀) := sqrt_pos.mpr (by positivity)
  have hall := ((hasFDerivAt_const B₀ p).add ((hr.const_mul (B₀ * η)).mul hy.cos)).add
    (h2.mul
      (((hasFDerivAt_const b₀ p).add ((hz.const_mul 2).cos.const_mul b₁)).add
        ((hy.const_mul 2).cos.const_mul B₂c)))
  convert hall using 1
  · funext q; simp only [nearAxisB, radius, Pi.add_apply, Pi.mul_apply]
  · refine ContinuousLinearMap.ext fun v => ?_
    simp only [FunLike.coe_add, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.coe_comp, Function.comp_apply, gradCLM_apply, nearAxisBψ, nearAxisBθ,
      nearAxisBφ, radius, Pi.add_apply, zero_add]
    have hr2 : √(2 * p.1 / B₀) ^ 2 = 2 * p.1 / B₀ := sq_sqrt (by positivity)
    generalize √(2 * p.1 / B₀) = r at hrpos hr2 ⊢
    have hx : p.1 = B₀ * r ^ 2 / 2 := by field_simp at hr2 ⊢; linarith
    rw [hx]
    field_simp
    ring

/-- The near-axis QA model as a vacuum Boozer field, with `ψ_p = ι₀ ψ` (constant transform)
and covariant toroidal component `G`. -/
@[expose] def field (B₀ η b₀ b₁ B₂c ι₀ G : ℝ) (hB₀ : 0 < B₀) : BoozerField where
  B := nearAxisB B₀ η b₀ b₁ B₂c
  Bψ := nearAxisBψ B₀ η b₀ b₁ B₂c
  Bθ ψ θ _ := nearAxisBθ B₀ η B₂c ψ θ
  Bφ ψ _ φ := nearAxisBφ B₀ b₁ ψ φ
  ψp x := ι₀ * x
  ι _ := ι₀
  G := G
  hasFDerivAt_B p hp := nearAxisB_hasFDerivAt hB₀ p hp
  hasDerivAt_ψp x _ := by simpa using (hasDerivAt_id x).const_mul ι₀

/-- **Exact symmetry defect** (QA, `ξ = ∂_φ`): `ξB = −2 b₁ r² sin 2φ`. -/
theorem nearAxis_symmetryDefect {B₀ η b₀ b₁ B₂c ι₀ G ψ θ φ : ℝ} (hB₀ : 0 < B₀) (hψ : 0 ≤ ψ) :
    symmetryDefect (field B₀ η b₀ b₁ B₂c ι₀ G hB₀) 0 1 ψ θ φ =
      -2 * b₁ * radius B₀ ψ ^ 2 * sin (2 * φ) := by
  simp only [symmetryDefect, field, nearAxisBφ, radius_sq hB₀ hψ]
  ring

/-- **`ε_QS(r) = 2|b₁| r²`**: on the surface `ψ` (radius `r`), the symmetry defect `|ξB|` has
supremum `2|b₁| r²`, attained at `φ = π/4`. -/
theorem nearAxis_epsQS {B₀ η b₀ b₁ B₂c ι₀ G ψ : ℝ} (hB₀ : 0 < B₀) (hψ : 0 ≤ ψ) :
    IsGreatest {e | ∃ θ φ, e = |symmetryDefect (field B₀ η b₀ b₁ B₂c ι₀ G hB₀) 0 1 ψ θ φ|}
      (2 * |b₁| * radius B₀ ψ ^ 2) := by
  refine ⟨⟨0, π / 4, ?_⟩, ?_⟩
  · rw [nearAxis_symmetryDefect hB₀ hψ, show 2 * (π / 4) = π / 2 by ring, sin_pi_div_two]
    rw [show -2 * b₁ * radius B₀ ψ ^ 2 * 1 = -(2 * b₁ * radius B₀ ψ ^ 2) by ring, abs_neg,
      abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (radius B₀ ψ))]
    norm_num
  · rintro e ⟨θ, φ, rfl⟩
    rw [nearAxis_symmetryDefect hB₀ hψ, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (sq_nonneg (radius B₀ ψ))]
    have := abs_sin_le_one (2 * φ)
    have h0 : 0 ≤ |b₁| * radius B₀ ψ ^ 2 := by positivity
    norm_num
    nlinarith

/-- Defect bound on the tube `r ≤ r_c`: `|ξB| ≤ 2|b₁| r_c²`. -/
theorem nearAxis_symmetryDefect_le {B₀ η b₀ b₁ B₂c ι₀ G ψ θ φ rc : ℝ} (hB₀ : 0 < B₀)
    (hψ : 0 ≤ ψ) (hr : radius B₀ ψ ≤ rc) :
    |symmetryDefect (field B₀ η b₀ b₁ B₂c ι₀ G hB₀) 0 1 ψ θ φ| ≤ 2 * |b₁| * rc ^ 2 := by
  have hg := nearAxis_epsQS (η := η) (b₀ := b₀) (b₁ := b₁) (B₂c := B₂c) (ι₀ := ι₀) (G := G)
    hB₀ hψ
  have h1 := hg.2 ⟨θ, φ, rfl⟩
  have hr0 : 0 ≤ radius B₀ ψ := sqrt_nonneg _
  refine h1.trans ?_
  gcongr

/-- **Field range** on the tube `r ≤ r_c`:
`|B − B₀| ≤ B₀|η| r_c + r_c² (|b₀| + |b₁| + |B₂c|)`. -/
theorem nearAxis_abs_sub_le {B₀ η b₀ b₁ B₂c ψ θ φ rc : ℝ} (hB₀ : 0 < B₀) (hψ : 0 ≤ ψ)
    (hr : radius B₀ ψ ≤ rc) :
    |nearAxisB B₀ η b₀ b₁ B₂c ψ θ φ - B₀| ≤ B₀ * |η| * rc + rc ^ 2 * (|b₀| + |b₁| + |B₂c|) := by
  have hr0 : 0 ≤ radius B₀ ψ := sqrt_nonneg _
  have hsq : 2 * ψ / B₀ ≤ rc ^ 2 := by
    rw [← radius_sq hB₀ hψ]; gcongr
  have e : nearAxisB B₀ η b₀ b₁ B₂c ψ θ φ - B₀ = B₀ * η * radius B₀ ψ * cos θ +
      2 * ψ / B₀ * (b₀ + b₁ * cos (2 * φ) + B₂c * cos (2 * θ)) := by
    unfold nearAxisB; ring
  rw [e]
  have hq0 : 0 ≤ 2 * ψ / B₀ := by positivity
  have c1 := abs_cos_le_one θ
  have c2 := abs_cos_le_one (2 * φ)
  have c3 := abs_cos_le_one (2 * θ)
  have t1 : |B₀ * η * radius B₀ ψ * cos θ| ≤ B₀ * |η| * rc := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hB₀, abs_of_nonneg hr0]
    have : |η| * radius B₀ ψ ≤ |η| * rc := by gcongr
    have h2 : |η| * radius B₀ ψ * |cos θ| ≤ |η| * radius B₀ ψ := by
      have := mul_le_mul_of_nonneg_left c1 (by positivity : 0 ≤ |η| * radius B₀ ψ)
      linarith
    nlinarith
  have t2 : |b₀ + b₁ * cos (2 * φ) + B₂c * cos (2 * θ)| ≤ |b₀| + |b₁| + |B₂c| := by
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ((abs_add_le _ _).trans (add_le_add le_rfl ?_)) ?_
    · rw [abs_mul]; nlinarith [abs_nonneg b₁]
    · rw [abs_mul]; nlinarith [abs_nonneg B₂c]
  have t3 : |2 * ψ / B₀ * (b₀ + b₁ * cos (2 * φ) + B₂c * cos (2 * θ))| ≤
      rc ^ 2 * (|b₀| + |b₁| + |B₂c|) := by
    rw [abs_mul, abs_of_nonneg hq0]
    exact mul_le_mul hsq t2 (abs_nonneg _) (by positivity)
  exact (abs_add_le _ _).trans (add_le_add t1 t3)

/-! ## Normalized precise-QA fit (pyQSC "precise QA", `R ≈ 1 m`, `B₀ = 1 T`) -/

/-- Normalized precise-QA model: `B₀ = 1`, `η = −339/500`, `b₀ = −111/500`, `b₁ = −7/1000`,
`B₂c = 67/250`, `ι₀ = 211/500`, `G = 107/100`. Agrees with a real field only to the order of
the near-axis expansion. -/
@[expose] def preciseQA : BoozerField :=
  field 1 (-339 / 500) (-111 / 500) (-7 / 1000) (67 / 250) (211 / 500) (107 / 100) one_pos

/-- `ε_QS(r) = (7/500) r²` for the normalized precise-QA model. -/
theorem preciseQA_epsQS {ψ : ℝ} (hψ : 0 ≤ ψ) :
    IsGreatest {e | ∃ θ φ, e = |symmetryDefect preciseQA 0 1 ψ θ φ|}
      (7 / 500 * radius 1 ψ ^ 2) := by
  have := nearAxis_epsQS (B₀ := 1) (η := -339 / 500) (b₀ := -111 / 500) (b₁ := -7 / 1000)
    (B₂c := 67 / 250) (ι₀ := 211 / 500) (G := 107 / 100) one_pos hψ
  rw [show preciseQA = field 1 (-339 / 500) (-111 / 500) (-7 / 1000) (67 / 250) (211 / 500)
    (107 / 100) one_pos from rfl]
  convert this using 1
  norm_num [abs_of_neg]

/-! ## Reactor-scale model and 3.5 MeV alphas -/

/-- Reactor-scale QA model: the precise-QA fit scaled to minor radius `a = 1.7 m` (aspect
ratio 6, length scale ≈ 9.59) and `B₀ = 5.7 T`, rounded: `η = −0.07 m⁻¹`,
`b₀ = −0.0137 T/m²`, `b₁ = −4.3 × 10⁻⁴ T/m²`, `B₂c = 0.0165 T/m²`, `ι₀ = 211/500`,
`G = 58.1 T m`. Agrees with a real field only to the order of the near-axis expansion. -/
@[expose] def reactorQA : BoozerField :=
  field (57 / 10) (-7 / 100) (-137 / 10000) (-43 / 100000) (33 / 2000) (211 / 500) (581 / 10)
    (by norm_num)

/-- Flux at the edge `r = a = 1.7 m`: `ψ_a = B₀ a²/2 = 8.2365 T m²`. -/
@[expose] def psiEdge : ℝ := 57 / 10 * (17 / 10) ^ 2 / 2

/-- Flux at the start radius `r = a/4`: `B₀ (a/4)²/2 = 0.51478125 T m²`. -/
@[expose] def psiStart : ℝ := 57 / 10 * (17 / 40) ^ 2 / 2

/-- Alpha mass (kg), rounded CODATA, as in `GuidingCentre`. -/
@[expose] def mα : ℝ := 6.6447e-27
/-- Alpha charge `2e` (C). -/
@[expose] def qα : ℝ := 2 * 1.6022e-19
/-- Alpha birth energy `3.5 MeV` (J). -/
@[expose] def Eα : ℝ := 3.5e6 * 1.6022e-19

/-- `ε_QS(a) = 2|b₁| a² = 0.0024854 T` (≈ 4.4 × 10⁻⁴ B₀) for the reactor model. -/
theorem reactorQA_epsQS_edge :
    IsGreatest {e | ∃ θ φ, e = |symmetryDefect reactorQA 0 1 psiEdge θ φ|} 0.0024854 := by
  have := nearAxis_epsQS (B₀ := 57 / 10) (η := -7 / 100) (b₀ := -137 / 10000)
    (b₁ := -43 / 100000) (B₂c := 33 / 2000) (ι₀ := 211 / 500) (G := 581 / 10) (by norm_num)
    (ψ := psiEdge) (by norm_num [psiEdge])
  rw [radius_sq (by norm_num) (by norm_num [psiEdge])] at this
  rw [show reactorQA = field (57 / 10) (-7 / 100) (-137 / 10000) (-43 / 100000) (33 / 2000)
    (211 / 500) (581 / 10) (by norm_num) from rfl]
  convert this using 1
  norm_num [psiEdge, abs_of_neg]

/-- For `ψ ≤ ψ_a`, the radius is at most `a = 1.7`. -/
theorem radius_le_edge {ψ : ℝ} (hc : ψ ≤ psiEdge) : radius (57 / 10) ψ ≤ 17 / 10 := by
  rw [radius, show (17 / 10 : ℝ) = √((17 / 10) ^ 2) by rw [sqrt_sq (by norm_num)]]
  apply sqrt_le_sqrt
  unfold psiEdge at hc
  linarith

/-- Field range of the reactor model on `0 < ψ ≤ ψ_a`: `4.93 ≤ B ≤ 6.47` T. -/
theorem reactorQA_B_bounds {ψ θ φ : ℝ} (hψ : 0 < ψ) (hc : ψ ≤ psiEdge) :
    4.93 ≤ reactorQA.B ψ θ φ ∧ reactorQA.B ψ θ φ ≤ 6.47 := by
  have h := nearAxis_abs_sub_le (η := -7 / 100) (b₀ := -137 / 10000) (b₁ := -43 / 100000)
    (B₂c := 33 / 2000) (θ := θ) (φ := φ) (by norm_num : (0 : ℝ) < 57 / 10) hψ.le
    (radius_le_edge hc)
  change 4.93 ≤ nearAxisB (57 / 10) (-7 / 100) (-137 / 10000) (-43 / 100000) (33 / 2000) ψ θ φ ∧
    nearAxisB (57 / 10) (-7 / 100) (-137 / 10000) (-43 / 100000) (33 / 2000) ψ θ φ ≤ 6.47
  rw [abs_le] at h
  norm_num [abs_of_neg] at h
  constructor <;> linarith [h.1, h.2]

/-- Orbit-width bound `Δρ` (m) for passing alphas (`|v_∥/v| ≥ 0.9`) on `r ≤ a`, from
`rho_deviation_passing` with `B ∈ [4.93, 6.47]`, `w = 9 × 10⁶ m/s`, `U = 1.3 × 10⁷ m/s`. -/
@[expose] def alphaΔρ : ℝ :=
  mα / |qα| * ((6.47 - 4.93) / 4.93 ^ 2) * (2 * Eα / mα / (2 * 9e6) + 1.3e7)

/-- `Δρ < 2.95 cm`; the orbit-width term `|G| Δρ/ι₀` is below `4.07 T m²`. -/
theorem alphaΔρ_lt : alphaΔρ < 0.0295 := by
  norm_num [alphaΔρ, mα, qα, Eα, abs_of_pos]

/-- **3.5 MeV alpha confinement in the reactor-scale near-axis QA model.** Every guiding-centre
orbit (solving the equations only on `[0, 8 × 10⁻⁴ s]`) of the vacuum Boozer model
with field `reactorQA` (a = 1.7 m, B₀ = 5.7 T) for an alpha
(`m = 6.6447 × 10⁻²⁷ kg`, `q = 2e`) of energy `3.5 MeV`, any `μ ≥ 0`, passing pitch
`v_∥² ≥ 0.81 v²` (`|v_∥/v| ≥ 0.9`), starting at `ψ ≤ B₀(a/4)²/2` (i.e. `r ≤ a/4`), satisfies
`ψ(t) ≤ 8.2 T m² < ψ_a = 8.2365 T m²` for `0 ≤ t ≤ 8 × 10⁻⁴ s`.

This is a statement about the model only: the field agrees with a real vacuum field only to
the order of the near-axis expansion, and the Boozer guiding-centre equations are assumed.
`0.8 ms` is ~500 times shorter than the slowing-down time (≈ 0.4 s) because the drift bound
is linear in the defect `ε_QS(a) = 0.0024854 T` (no averaging of the oscillating `sin 2φ`). -/
theorem alpha_trapped_reactorQA {μ : ℝ} {ψ θ φ ρ : ℝ → ℝ} (hμ : 0 ≤ μ)
    (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ 8e-4)
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα)
    (hpitch : 81 / 100 * (2 * Eα / mα) ≤ parallelVelocity reactorQA mα qα ψ θ φ ρ 0 ^ 2)
    (hstart : ψ 0 ≤ psiStart) :
    ∀ t ∈ Set.Icc 0 8e-4, ψ t ≤ 8.2 := by
  have hm : 0 < mα := by norm_num [mα]
  have hq : qα ≠ 0 := by norm_num [qα]
  have hGv : reactorQA.G = 581 / 10 := rfl
  have hG : reactorQA.G ≠ 0 := by rw [hGv]; norm_num
  have hs0 : ψ 0 ≤ 0.51478125 := by norm_num [psiStart] at hstart; linarith
  refine boozerGC_trapped_until (N := 0) (M := 1) (c := psiEdge) (ιmin := 211 / 500)
    (Bmin := 4.93) (ε := 0.0024854) (Δρ := alphaΔρ) hm hq hG hμ h
    (by norm_num [psiEdge]) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (fun x _ _ hx hxc => (reactorQA_B_bounds hx hxc).1) ?_ ?_ ?_ ?_
  · intro x θ' φ' hx hxc
    have := nearAxis_symmetryDefect_le (η := -7 / 100) (b₀ := -137 / 10000)
      (b₁ := -43 / 100000) (B₂c := 33 / 2000) (ι₀ := 211 / 500) (G := 581 / 10) (θ := θ')
      (φ := φ') (by norm_num : (0 : ℝ) < 57 / 10) hx.le (radius_le_edge hxc)
    refine this.trans (le_of_eq ?_)
    norm_num [abs_of_neg]
  · intro x hx _
    have hp : ∀ y, reactorQA.ψp y = 211 / 500 * y := fun _ => rfl
    rw [hp, hp, le_abs]
    right; linarith
  · intro t ht hhist
    have := rho_deviation_passing (Bmin := 4.93) (Bmax := 6.47) (w := 9e6) (U := 1.3e7)
      hm hq hG hμ (h.mono ht.2) (by norm_num) (by norm_num) ht.1
      (fun s hs => reactorQA_B_bounds (h.pos s ⟨hs.1, hs.2.trans ht.2⟩) (hhist s hs)) ?_ ?_
      (by norm_num)
    · rw [hE] at this; exact this
    · rw [hE]
      have : (9e6 : ℝ) ^ 2 + 2 * Eα / mα * (6.47 - 4.93) / 4.93 ≤ 81 / 100 * (2 * Eα / mα) := by
        norm_num [Eα, mα]
      linarith
    · rw [hE]; norm_num [Eα, mα]
  · rw [hE, hGv]
    have h1 := alphaΔρ_lt
    have h2 : 2 * Eα / (|qα| * 4.93) * 0.0024854 * 8e-4 ≤ 1.4117 := by
      norm_num [Eα, qα, abs_of_pos]
    have h3 : 0 ≤ alphaΔρ := by unfold alphaΔρ; norm_num [mα, qα, Eα, abs_of_pos]
    norm_num
    nlinarith

/-- In radius terms: under the hypotheses of `alpha_trapped_reactorQA` the alpha stays strictly
inside the edge, `r(t) < a = 1.7 m`, for `0 ≤ t ≤ 8 × 10⁻⁴ s`. -/
theorem alpha_radius_lt_edge {μ : ℝ} {ψ θ φ ρ : ℝ → ℝ} (hμ : 0 ≤ μ)
    (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ 8e-4)
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα)
    (hpitch : 81 / 100 * (2 * Eα / mα) ≤ parallelVelocity reactorQA mα qα ψ θ φ ρ 0 ^ 2)
    (hstart : ψ 0 ≤ psiStart) (t : ℝ) (ht : t ∈ Set.Icc 0 8e-4) :
    radius (57 / 10) (ψ t) < 17 / 10 := by
  have h1 := alpha_trapped_reactorQA hμ h hE hpitch hstart t ht
  rw [radius, show (17 / 10 : ℝ) = √((17 / 10) ^ 2) by rw [sqrt_sq (by norm_num)]]
  apply sqrt_lt_sqrt (by have := h.pos t ht; positivity)
  linarith

/-- Required defect for slowing-down-time confinement (same argument, same orbit-width term):
the gap of `boozerGC_trapped_until` closes for `T = 0.4 s` at `ε = 5 × 10⁻⁶ T ≈ 9 × 10⁻⁷ B₀`,
about 500 times smaller than the model's `ε_QS(a) = 2.5 × 10⁻³ T`. -/
theorem required_defect_slowingDown :
    |(1 : ℝ) * (581 / 10)| * 0.0295 + 2 * Eα / (|qα| * 4.93) * 5e-6 * 0.4 ≤
      211 / 500 * (8.2 - psiStart) ∧
    (0.0024854 : ℝ) / 5e-6 > 490 := by
  norm_num [Eα, qα, psiStart, abs_of_pos]

/-- Sanity (honest comparison): the proved horizon `8 × 10⁻⁴ s` is less than `1/400` of a
0.4 s slowing-down time. -/
theorem horizon_vs_slowingDown : (8e-4 : ℝ) < 0.4 / 400 := by norm_num

end PlasmaLean.Design.NearAxisQA
