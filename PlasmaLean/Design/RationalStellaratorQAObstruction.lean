/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorAxis
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The first-order quasi-axisymmetry obstruction for the planar-axis rotating ellipse

Research note `notes/theory/rational-field-c2.md` (N-30, §4); question Q-19 (clause C2 of the
stellarator contract). Source of the statement: D. A. Garren, A. H. Boozer, *Phys. Fluids B* 3
(1991) 2805, 2822 (a planar magnetic axis in vacuum admits no quasisymmetry with `ι₀ ≠ 0` at
first order); here it is proved directly for the rotating-ellipse family of N-9 §1.3, to which
`RationalStellarator.field ε` belongs (`N = 2`).

## The family (general `N`, pure algebra)

The linearized field-line flow about the planar circular axis `R = 1, z = 0` of an `N`-period
rotating ellipse is `v = Rot(Nφ/2) w`, `w' = M w`, `M = [[2ε, N/2], [−N/2, −2ε]]`, with
`κ = √(N²/4 − 4ε²)` (`kappaN`) and on-axis transform `ι₀ = N/2 − κ` (`iotaN`). Its invariant
tori, written in the straight-field-line angles `(θ_s, φ)` of the linear flow, carry the
first-order coefficient of `‖B‖ = 1/R + O(r²)` in the distance `r` from the axis (`b1`)

`b1 θ φ = −(a cos θ + ε sin θ) − (c cos(Nφ − θ) + ε sin(Nφ − θ))`,
`a = (N/2 + κ)/2`, `c = (N/2 − κ)/2`,

split as `qaPart` (a function of `θ` alone: helicity `(1, 0)`) plus `nonQAPart` (the
`(1, 1)` sideband `cos(θ − Nφ)`). Results:

* `nonQAAmp_sq`, `qaAmp_sq`: the amplitudes satisfy `|P|² = N ι₀ / 4`, `|Q|² = N (N − ι₀)/4`
  (`|P|² + |Q|² = N²/4`, independent of `ε`);
* `nonQA_fraction`: the non-QA fraction of the first-order variation is exactly `√(ι₀/N)`;
* `b1_not_quasiSymmetric`: if `ι₀ ≠ 0`, `b1` is **not quasisymmetric for any helicity**
  `(M, K) ≠ (0, 0)`: it is not a function of `Mθ − K N φ`;
* `rotatingEllipse_firstOrder_QA_defect`: the sup-distance of `b1` from the QA functions
  (functions of `θ` alone) is exactly the non-QA amplitude `√(N ι₀)/2`, attained by `qaPart`;
  it is positive iff `ι₀ ≠ 0` (`nonQAAmp_pos_iff`).

## The actual field (`N = 2`)

For `RationalStellarator.field ε`, `0 < 4ε² < 1`:

* `normField_hasFDerivAt_axis`: the actual Fréchet derivative of `‖B‖` at the axis point
  `axis φ` is `v ↦ −⟪e_R(φ), v⟫` (first-order `‖B‖ = 1 − (R − 1)`);
* `linTorus`, `linTorus_eq_Φ`, `linTorus_hasDerivAt`: the linearized invariant tori
  `v(θ₀, φ) = Rot(φ) (cos ϑ, −κ sin ϑ − 2ε cos ϑ)`, `ϑ = θ₀ + κφ`, solve the variational
  equation `v' = 2ε S(φ) v` of the actual axis (`axis_jacobian`, `Φ_solves`);
* `firstOrderNormB_eq_b1`: the first-order `‖B‖` of the actual field on these tori,
  `d/dr ‖B(axis φ + r v)‖ |_{r=0}` (`firstOrderNormB_hasDerivAt`), written in the
  straight-field-line angles `θ_s = ι₀ φ − θ₀`, is exactly `b1 2 ε θ_s φ`;
* `rationalStellarator_firstOrder_not_QS`: hence it is not quasisymmetric for any helicity, and
  `rationalStellarator_firstOrder_QA_defect`: its QA defect is `√(2 ι₀)/2`, a fraction `√(ι₀/2)`;
* `nonQA_fraction_quarter`: at `ε = 1/4`, `ι₀ = 1 − √3/2` and `0.2588 < √(ι₀/2) < 0.2589`
  (numerics of N-30 §3.2: 0.259 at `r = 0.05`).

Sanity: `b1_zero_iota` (the axisymmetric limit `ε = 0`, `ι₀ = 0`: `b1 = −(N/2) cos θ` is QA, zero
defect), `nonQA_fraction_quarter` (numeric instance).

**What is first-order only.** Everything is about the first-order coefficient in the distance
`r` from the axis: the derivative of `‖B‖` at the axis and the linearized tori. The angles are the
straight-field-line angles `(θ_s, φ)` of the linearized flow; that they agree with Boozer angles
up to `O(r²)` (`φ_B = φ + εh`, `θ_B = θ_s + ιεh`, `h = O(r²)`, N-30 §2) is proved informally and
not formalized. Nothing is claimed about the `O(r²)` terms or about the nonlinear tori.

## Contract reading

`RationalStellarator.field (1/4)` satisfies **C1** (vacuum, current-free with `ι ≥ ι_A` on a
certified torus: `field_vacuum`,
`RationalStellaratorContract.rationalStellarator_currentFreeTransform`)
and **C4** (KAM torus, field lines confined forever: `rationalStellarator_confined_forever`). But
it cannot be quasi-axisymmetric (nor quasisymmetric with any helicity) **even at first order** in
the distance from the axis: the defect is pinned at the fraction `√(ι₀/N)` of the first-order
variation, and the defect/ι ratio `1/√(N ι₀)` grows as `ι₀ → 0`. So the quasisymmetry route to C2
(Q-23: `Kinetic.Boozer.omnigenousOn_of_exactQS`, `approxOmnigenousOn_of_defect_le`, which need a
QS defect small relative to `ι`) cannot give a small relative defect for this field at first
order (linearized straight-field-line angles, N = 2; no link to a Boozer model is formalized). A
QS-based C2 candidate therefore needs a different axis geometry; Garren–Boozer suggests a
non-planar axis (not proved here). Quasi-isodynamic routes are not addressed.
-/

public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorQAObstruction

open Real

/-! ## The rotating-ellipse family: first-order `‖B‖` and its Fourier split -/

/-- `κ_N = √(N²/4 − 4ε²)`: rotation frequency of the linear flow in the frame co-rotating with
the ellipse. -/
@[expose] def kappaN (N ε : ℝ) : ℝ := √(N ^ 2 / 4 - 4 * ε ^ 2)

/-- On-axis rotational transform `ι₀ = N/2 − κ_N` of the `N`-period rotating ellipse. -/
@[expose] def iotaN (N ε : ℝ) : ℝ := N / 2 - kappaN N ε

/-- Cosine coefficient `a = (N/2 + κ)/2` of the QA (helicity `(1, 0)`) harmonic. -/
@[expose] def qaCos (N ε : ℝ) : ℝ := (N / 2 + kappaN N ε) / 2

/-- Cosine coefficient `c = (N/2 − κ)/2 = ι₀/2` of the non-QA (`(1, 1)`) harmonic. -/
@[expose] def nonQACos (N ε : ℝ) : ℝ := (N / 2 - kappaN N ε) / 2

/-- The QA part of the first-order `‖B‖`: `−(a cos θ + ε sin θ)`, a function of `θ` only. -/
@[expose] def qaPart (N ε θ : ℝ) : ℝ := -(qaCos N ε * cos θ + ε * sin θ)

/-- The non-QA part: `−(c cos(Nφ − θ) + ε sin(Nφ − θ))`, the helical sideband. -/
@[expose] def nonQAPart (N ε θ φ : ℝ) : ℝ :=
  -(nonQACos N ε * cos (N * φ - θ) + ε * sin (N * φ - θ))

/-- **The first-order coefficient of `‖B‖`** on the linearized tori of the rotating ellipse, in
the straight-field-line angles `(θ, φ)`: `‖B‖ = 1 + r · b1 θ φ + O(r²)`. -/
@[expose] def b1 (N ε θ φ : ℝ) : ℝ := qaPart N ε θ + nonQAPart N ε θ φ

/-- Amplitude `|Q| = √(a² + ε²)` of the QA harmonic. -/
@[expose] def qaAmp (N ε : ℝ) : ℝ := √(qaCos N ε ^ 2 + ε ^ 2)

/-- Amplitude `|P| = √(c² + ε²)` of the non-QA harmonic. -/
@[expose] def nonQAAmp (N ε : ℝ) : ℝ := √(nonQACos N ε ^ 2 + ε ^ 2)

/-- `b1` is quasisymmetric with helicity `(M, K)` (per field period `N`): it is a function of
`Mθ − K N φ`. Helicity `(1, 0)` is quasi-axisymmetry. -/
@[expose] def IsQuasiSymmetric (b : ℝ → ℝ → ℝ) (N M K : ℝ) : Prop :=
  ∃ f : ℝ → ℝ, ∀ θ φ, b θ φ = f (M * θ - K * N * φ)

section Family

variable {N ε : ℝ}

/-- `κ² = N²/4 − 4ε²` when `16ε² ≤ N²`. -/
theorem kappaN_sq (h : 16 * ε ^ 2 ≤ N ^ 2) : kappaN N ε ^ 2 = N ^ 2 / 4 - 4 * ε ^ 2 :=
  Real.sq_sqrt (by linarith)

/-- `κ ≥ 0`. -/
theorem kappaN_nonneg : 0 ≤ kappaN N ε := Real.sqrt_nonneg _

/-- `κ ≤ N/2` (for `N > 0`). -/
theorem kappaN_le (hN : 0 < N) (h : 16 * ε ^ 2 ≤ N ^ 2) : kappaN N ε ≤ N / 2 := by
  have := kappaN_sq h
  nlinarith [kappaN_nonneg (N := N) (ε := ε), sq_nonneg ε]

/-- `ι₀ ≥ 0`. -/
theorem iotaN_nonneg (hN : 0 < N) (h : 16 * ε ^ 2 ≤ N ^ 2) : 0 ≤ iotaN N ε := by
  have := kappaN_le hN h
  unfold iotaN; linarith

/-- **`|P|² = N ι₀ / 4`**: the squared non-QA amplitude. -/
theorem nonQAAmp_sq (h : 16 * ε ^ 2 ≤ N ^ 2) : nonQAAmp N ε ^ 2 = N * iotaN N ε / 4 := by
  have hk := kappaN_sq h
  rw [nonQAAmp, Real.sq_sqrt (by positivity), nonQACos, iotaN]
  linear_combination hk / 4

/-- **`|Q|² = N (N − ι₀) / 4`**: the squared QA amplitude. -/
theorem qaAmp_sq (h : 16 * ε ^ 2 ≤ N ^ 2) : qaAmp N ε ^ 2 = N * (N - iotaN N ε) / 4 := by
  have hk := kappaN_sq h
  rw [qaAmp, Real.sq_sqrt (by positivity), qaCos, iotaN]
  linear_combination hk / 4

/-- `|P|² + |Q|² = N²/4`, independent of `ε`. -/
theorem amp_sq_sum (h : 16 * ε ^ 2 ≤ N ^ 2) : qaAmp N ε ^ 2 + nonQAAmp N ε ^ 2 = N ^ 2 / 4 := by
  rw [qaAmp_sq h, nonQAAmp_sq h]; ring

/-- The non-QA amplitude in closed form: `|P| = √(N ι₀)/2`. -/
theorem nonQAAmp_eq (hN : 0 < N) (h : 16 * ε ^ 2 ≤ N ^ 2) :
    nonQAAmp N ε = √(N * iotaN N ε) / 2 := by
  have hι := iotaN_nonneg hN h
  have h0 : 0 ≤ nonQAAmp N ε := Real.sqrt_nonneg _
  have h1 : 0 ≤ √(N * iotaN N ε) := Real.sqrt_nonneg _
  have h2 : √(N * iotaN N ε) ^ 2 = N * iotaN N ε := Real.sq_sqrt (by positivity)
  nlinarith [nonQAAmp_sq h]

/-- **The non-QA fraction of the first-order `‖B‖` variation is `√(ι₀/N)`**:
`|P| / √(|P|² + |Q|²) = √(ι₀/N)`. -/
theorem nonQA_fraction (hN : 0 < N) (h : 16 * ε ^ 2 ≤ N ^ 2) :
    nonQAAmp N ε / √(qaAmp N ε ^ 2 + nonQAAmp N ε ^ 2) = √(iotaN N ε / N) := by
  have hι := iotaN_nonneg hN h
  rw [amp_sq_sum h, show N ^ 2 / 4 = (N / 2) ^ 2 by ring, Real.sqrt_sq (by linarith)]
  have h0 : 0 ≤ nonQAAmp N ε := Real.sqrt_nonneg _
  have h1 : 0 ≤ √(iotaN N ε / N) := Real.sqrt_nonneg _
  have h2 : √(iotaN N ε / N) ^ 2 = iotaN N ε / N := Real.sq_sqrt (by positivity)
  have h3 := nonQAAmp_sq h
  rw [div_eq_iff (by positivity)]
  have h4 : (√(iotaN N ε / N) * (N / 2)) ^ 2 = nonQAAmp N ε ^ 2 := by
    rw [mul_pow, h2, h3]; field_simp; ring
  have h5 : 0 ≤ √(iotaN N ε / N) * (N / 2) := by positivity
  nlinarith [sq_nonneg (nonQAAmp N ε - √(iotaN N ε / N) * (N / 2)),
    sq_nonneg (nonQAAmp N ε + √(iotaN N ε / N) * (N / 2))]

/-- `ι₀ = 0` iff `ε = 0` (for `N > 0`). -/
theorem iotaN_eq_zero_iff (hN : 0 < N) (h : 16 * ε ^ 2 ≤ N ^ 2) : iotaN N ε = 0 ↔ ε = 0 := by
  have hk := kappaN_sq h
  constructor
  · intro h0
    have : kappaN N ε = N / 2 := by unfold iotaN at h0; linarith
    rw [this] at hk
    nlinarith [sq_nonneg ε]
  · intro h0
    subst h0
    have : kappaN N 0 = N / 2 := by
      rw [kappaN, show N ^ 2 / 4 - 4 * (0 : ℝ) ^ 2 = (N / 2) ^ 2 by ring,
        Real.sqrt_sq (by linarith)]
    simp [iotaN, this]

/-- The non-QA amplitude is positive iff `ι₀ ≠ 0`. -/
theorem nonQAAmp_pos_iff (hN : 0 < N) (h : 16 * ε ^ 2 ≤ N ^ 2) :
    0 < nonQAAmp N ε ↔ iotaN N ε ≠ 0 := by
  have hι := iotaN_nonneg hN h
  rw [nonQAAmp_eq hN h]
  constructor
  · intro hp h0
    rw [h0, mul_zero, Real.sqrt_zero] at hp
    linarith
  · intro h0
    have : 0 < N * iotaN N ε := mul_pos hN (lt_of_le_of_ne hι (Ne.symm h0))
    positivity

/-- The QA cosine coefficient is positive (`a ≥ N/4 > 0`). -/
theorem qaCos_pos (hN : 0 < N) : 0 < qaCos N ε := by
  have := kappaN_nonneg (N := N) (ε := ε)
  unfold qaCos; linarith

/-- The non-QA part is bounded by its amplitude. -/
theorem abs_nonQAPart_le (θ φ : ℝ) : |nonQAPart N ε θ φ| ≤ nonQAAmp N ε := by
  rw [nonQAPart, abs_neg]
  apply Real.abs_le_sqrt
  have := sin_sq_add_cos_sq (N * φ - θ)
  nlinarith [sq_nonneg (nonQACos N ε * sin (N * φ - θ) - ε * cos (N * φ - θ))]

/-- The non-QA part attains `±` its amplitude at fixed `θ`. -/
theorem exists_nonQAPart_eq (hN : N ≠ 0) (θ : ℝ) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ∃ φ, nonQAPart N ε θ φ = s * nonQAAmp N ε := by
  by_cases hz : nonQACos N ε = 0 ∧ ε = 0
  · obtain ⟨h1, h2⟩ := hz
    refine ⟨0, ?_⟩
    rw [nonQAPart, nonQAAmp, h1, h2]
    simp
  set z : ℂ := ⟨nonQACos N ε, ε⟩
  have hz0 : z ≠ 0 := by
    intro h0
    apply hz
    exact ⟨congrArg Complex.re h0, congrArg Complex.im h0⟩
  have hn : ‖z‖ = nonQAAmp N ε := by
    rw [Complex.norm_def, Complex.normSq_apply, nonQAAmp]
    congr 1; simp [z]; ring
  have hnpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hc := Complex.cos_arg hz0
  have hsn := Complex.sin_arg z
  have key : nonQACos N ε * cos (Complex.arg z) + ε * sin (Complex.arg z) = ‖z‖ := by
    rw [hc, hsn]
    have h2 : ‖z‖ ^ 2 = nonQACos N ε ^ 2 + ε ^ 2 := by
      rw [hn, nonQAAmp, Real.sq_sqrt (by positivity)]
    field_simp
    simp only [z] at h2 ⊢
    linarith
  rcases hs with rfl | rfl
  · refine ⟨(Complex.arg z + π + θ) / N, ?_⟩
    rw [nonQAPart, show N * ((Complex.arg z + π + θ) / N) - θ = Complex.arg z + π by
      field_simp; ring, cos_add_pi, sin_add_pi, ← hn]
    linear_combination key
  · refine ⟨(Complex.arg z + θ) / N, ?_⟩
    rw [nonQAPart, show N * ((Complex.arg z + θ) / N) - θ = Complex.arg z by
      field_simp; ring, ← hn]
    linear_combination -key

/-- Parity: shifting `(θ, φ) ↦ (θ + π, φ + π/N)` flips the QA part and keeps the non-QA part. -/
theorem parts_shift (hN : N ≠ 0) (θ φ : ℝ) :
    qaPart N ε (θ + π) = -qaPart N ε θ ∧
      nonQAPart N ε (θ + π) (φ + π / N) = nonQAPart N ε θ φ := by
  refine ⟨by simp [qaPart, cos_add_pi, sin_add_pi]; ring, ?_⟩
  rw [nonQAPart, nonQAPart, show N * (φ + π / N) - (θ + π) = N * φ - θ by field_simp; ring]

/-- **Garren–Boozer for the planar-axis rotating ellipse, first order.** If `ι₀ ≠ 0`, the
first-order `‖B‖` is not quasisymmetric for **any** helicity `(M, K) ≠ (0, 0)`. -/
theorem b1_not_quasiSymmetric (hN : 0 < N) (h : 16 * ε ^ 2 ≤ N ^ 2) (hι : iotaN N ε ≠ 0)
    {M K : ℝ} (hMK : M ≠ 0 ∨ K ≠ 0) : ¬ IsQuasiSymmetric (b1 N ε) N M K := by
  rintro ⟨f, hf⟩
  have hN0 : N ≠ 0 := hN.ne'
  -- invariance along the helical direction `(K N, M)`
  have inv : ∀ θ φ t, b1 N ε (θ + K * N * t) (φ + M * t) = b1 N ε θ φ := by
    intro θ φ t
    rw [hf, hf]; congr 1; ring
  -- the two parts are separately invariant
  have qinv : ∀ θ t, qaPart N ε (θ + K * N * t) = qaPart N ε θ := by
    intro θ t
    have e1 := inv θ 0 t
    have e2 := inv (θ + π) (π / N) t
    have s1 := parts_shift (ε := ε) hN0 θ 0
    have s2 := parts_shift (ε := ε) hN0 (θ + K * N * t) (M * t)
    rw [show θ + π + K * N * t = θ + K * N * t + π by ring,
      show π / N + M * t = M * t + π / N by ring] at e2
    simp only [b1] at e1 e2
    simp only [zero_add] at s1
    rw [s2.1, s2.2, s1.1, s1.2] at e2
    simp only [zero_add] at e1 e2
    linarith
  rcases eq_or_ne K 0 with hK | hK
  · have hM : M ≠ 0 := by
      rcases hMK with hM | hK'
      · exact hM
      · exact absurd hK hK'
    have pinv : ∀ θ φ t, nonQAPart N ε θ (φ + M * t) = nonQAPart N ε θ φ := by
      intro θ φ t
      have e1 := inv θ φ t
      simp only [b1, hK, zero_mul, add_zero] at e1
      linarith
    have hzero : ∀ θ φ, nonQAPart N ε θ φ = 0 := by
      intro θ φ
      have e := pinv θ φ (π / (N * M))
      rw [show φ + M * (π / (N * M)) = φ + π / N by field_simp, nonQAPart, nonQAPart,
        show N * (φ + π / N) - θ = (N * φ - θ) + π by field_simp; ring, cos_add_pi,
        sin_add_pi] at e
      rw [nonQAPart]
      linarith
    have hc : nonQACos N ε = 0 := by
      have := hzero 0 0; simpa [nonQAPart] using this
    have he : ε = 0 := by
      have := hzero (-(π / 2)) 0; simpa [nonQAPart, hc] using this
    exact hι ((iotaN_eq_zero_iff hN h).mpr he)
  · have hzero : qaPart N ε 0 = 0 := by
      have e := qinv 0 (π / (K * N))
      rw [show (0 : ℝ) + K * N * (π / (K * N)) = 0 + π by field_simp,
        (parts_shift (ε := ε) hN0 0 0).1] at e
      linarith
    have := qaCos_pos (ε := ε) hN
    simp [qaPart] at hzero
    linarith

/-- **The first-order QA defect of the rotating ellipse**, `rotatingEllipse_firstOrder_QA_defect`.
For `N > 0`, `16ε² ≤ N²`:
1. `b1 = qaPart + nonQAPart` with `qaPart` a function of `θ` alone (helicity `(1, 0)`);
2. the non-QA part is bounded by `|P| = √(N ι₀)/2`, so the QA function `qaPart` approximates
   `b1` to within `|P|` everywhere;
3. no function of `θ` alone does better: for every `f`, some `(θ, φ)` has `|b1 − f θ| ≥ |P|`;
4. the non-QA fraction is `√(ι₀/N)`, and `|P| > 0` iff `ι₀ ≠ 0`. -/
theorem rotatingEllipse_firstOrder_QA_defect (hN : 0 < N) (h : 16 * ε ^ 2 ≤ N ^ 2) :
    (∀ θ φ, b1 N ε θ φ - qaPart N ε θ = nonQAPart N ε θ φ) ∧
    (∀ θ φ, |b1 N ε θ φ - qaPart N ε θ| ≤ nonQAAmp N ε) ∧
    (∀ f : ℝ → ℝ, ∃ θ φ, nonQAAmp N ε ≤ |b1 N ε θ φ - f θ|) ∧
    nonQAAmp N ε = √(N * iotaN N ε) / 2 ∧
    nonQAAmp N ε / √(qaAmp N ε ^ 2 + nonQAAmp N ε ^ 2) = √(iotaN N ε / N) ∧
    (0 < nonQAAmp N ε ↔ iotaN N ε ≠ 0) := by
  have hsub : ∀ θ φ, b1 N ε θ φ - qaPart N ε θ = nonQAPart N ε θ φ := by
    intro θ φ; simp [b1]
  refine ⟨hsub, fun θ φ => by rw [hsub]; exact abs_nonQAPart_le θ φ, ?_, nonQAAmp_eq hN h,
    nonQA_fraction hN h, nonQAAmp_pos_iff hN h⟩
  intro f
  have hA : 0 ≤ nonQAAmp N ε := Real.sqrt_nonneg _
  rcases le_or_gt (qaPart N ε 0 - f 0) 0 with hx | hx
  · obtain ⟨φ, hφ⟩ := exists_nonQAPart_eq (ε := ε) hN.ne' 0 (-1) (Or.inr rfl)
    refine ⟨0, φ, ?_⟩
    rw [b1, hφ, abs_of_nonpos (by linarith)]
    linarith
  · obtain ⟨φ, hφ⟩ := exists_nonQAPart_eq (ε := ε) hN.ne' 0 1 (Or.inl rfl)
    refine ⟨0, φ, ?_⟩
    rw [b1, hφ, abs_of_pos (by linarith)]
    linarith

/-- **Sanity (axisymmetric limit).** At `ε = 0` (`ι₀ = 0`) the first-order `‖B‖` is the
tokamak-like `−(N/2) cos θ`: exactly QA, zero defect. -/
theorem b1_zero_iota (hN : 0 < N) (θ φ : ℝ) :
    b1 N 0 θ φ = -(N / 2 * cos θ) ∧ IsQuasiSymmetric (b1 N 0) N 1 0 ∧ nonQAAmp N 0 = 0 := by
  have hk : kappaN N 0 = N / 2 := by
    rw [kappaN, show N ^ 2 / 4 - 4 * (0 : ℝ) ^ 2 = (N / 2) ^ 2 by ring,
      Real.sqrt_sq (by linarith)]
  have hb : ∀ θ φ, b1 N 0 θ φ = -(N / 2 * cos θ) := by
    intro θ φ; simp [b1, qaPart, nonQAPart, qaCos, nonQACos, hk]
  refine ⟨hb θ φ, ⟨fun x => -(N / 2 * cos x), fun θ φ => by rw [hb]; simp⟩, ?_⟩
  simp [nonQAAmp, nonQACos, hk]

end Family

/-! ## The actual field (`N = 2`): first-order `‖B‖` on the linearized tori -/

section Field

open PlasmaLean.Fields PlasmaLean.Vacuum PlasmaLean.Design.RationalStellarator WithLp Matrix
open scoped RealInnerProductSpace

/-- On the axis, `⟪B, DB v⟫ = −⟪e_R, v⟫`: the field derivative has toroidal component
`−v_R` (from `∇φ = e_φ/R`; the helical part `ε∇h` is `O(r)` and its Jacobian at the axis has no
toroidal row). -/
theorem inner_field_fieldDeriv_axis (ε φ : ℝ) (v : Space) :
    ⟪field ε (axis φ), fieldDeriv ε (axis φ) v⟫ = -⟪eR φ, v⟫ := by
  have hcs : cos φ ^ 2 + sin φ ^ 2 = 1 := cos_sq_add_sin_sq φ
  have hr : r2 (axis φ) = 1 := by simp [r2, axis, hcs]
  have hw : winv (axis φ) = 1 := by simp [winv, hr]
  have hz : axis φ 2 = 0 := by simp [axis]
  have hA : Aq (axis φ) = 0 := by simp [Aq, hr, hz]
  have hB : Bq (axis φ) = 0 := by simp [Bq, hr, hz]
  have hY : Yp (axis φ) = 0 := by simp [Yp, hz]
  have hHn : Hnum (axis φ) = 0 := by simp [Hnum, hA, hB]
  have hH0 : H0 (axis φ) = 0 := by simp [H0, hr, hA, hB, hY]
  have hH1 : H1 (axis φ) = 0 := by simp [H1, hr, hA, hB, hY]
  have hH2 : H2 (axis φ) = 0 := by simp [H2, hz, hB]
  have h0 : axis φ 0 = cos φ := by simp [axis]
  have h1 : axis φ 1 = sin φ := by simp [axis]
  rw [field_axis]
  simp only [PiLp.inner_apply, Fin.sum_univ_three, fieldDeriv_apply',
      JB, JT, JG, wd, cv, cd, Hd, Hdd, H00, H01, H02, H11, H12, H22, hw, hHn, hH0, hH1, hH2,
      h0, h1, hz, eR, RCLike.inner_apply, conj_trivial,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination ((1/2) * sin φ * ε * v.ofLp 0 - 2 * sin φ * v.ofLp 1 -
    11/2 * cos φ ^ 2 * sin φ * ε * v.ofLp 0 - 11/2 * cos φ * sin φ ^ 2 * ε * v.ofLp 1 +
    1/2 * sin φ ^ 3 * ε * v.ofLp 0 + 1/2 * sin φ ^ 4 * ε * v.ofLp 2 - 2 * cos φ * v.ofLp 0 +
    5/2 * cos φ ^ 2 * ε * v.ofLp 2 + 1/2 * cos φ ^ 3 * ε * v.ofLp 1 -
    1/2 * cos φ ^ 4 * ε * v.ofLp 2 - 5/2 * sin φ ^ 2 * ε * v.ofLp 2 +
    1/2 * cos φ * ε * v.ofLp 1) * hcs

/-- **First-order `‖B‖` at the axis (actual derivative)**: `D‖B‖(axis φ) v = −⟪e_R(φ), v⟫`,
i.e. `‖B‖ = 1 − (R − 1) + O(r²)` near the axis, for every `ε`. -/
theorem normField_hasFDerivAt_axis (ε φ : ℝ) :
    HasFDerivAt (fun y => ‖field ε y‖) (-(innerSL ℝ (eR φ))) (axis φ) := by
  have hB := field_hasFDerivAt (axis φ) ε (axis_mem_domain φ)
  have hn : ‖field ε (axis φ)‖ = 1 := by
    rw [field_axis, EuclideanSpace.norm_eq, Fin.sum_univ_three]
    simp
  have hsq := hB.norm_sq.sqrt (by rw [hn]; norm_num)
  have he : (fun y => √(‖field ε y‖ ^ 2)) = fun y => ‖field ε y‖ := by
    funext y; exact Real.sqrt_sq (norm_nonneg _)
  rw [he] at hsq
  refine hsq.congr_fderiv ?_
  ext v
  simp [hn, inner_field_fieldDeriv_axis]

/-- The linearized invariant tori of the actual axis, in the poloidal plane `(R − 1, z)` at angle
`φ` (amplitude normalized to 1): `v(θ₀, φ) = Rot(φ) (cos ϑ, −κ sin ϑ − 2ε cos ϑ)`,
`ϑ = θ₀ + κφ`; `θ₀` labels the field line. -/
@[expose] def linTorus (ε θ₀ φ : ℝ) : Fin 2 → ℝ :=
  rot φ *ᵥ ![cos (θ₀ + κ ε * φ), -(κ ε) * sin (θ₀ + κ ε * φ) - 2 * ε * cos (θ₀ + κ ε * φ)]

/-- The linearized tori are orbits of the fundamental matrix: `v(θ₀, φ) = Φ(φ) v(θ₀, 0)`. -/
theorem linTorus_eq_Φ {ε : ℝ} (h : 4 * ε ^ 2 < 1) (θ₀ φ : ℝ) :
    linTorus ε θ₀ φ = Φ ε φ *ᵥ linTorus ε θ₀ 0 := by
  have hk := (κ_pos h).ne'
  have hr0 : rot 0 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [rot]
  rw [Φ, ← Matrix.mulVec_mulVec, linTorus, linTorus, hr0, Matrix.one_mulVec]
  congr 1
  ext i
  fin_cases i <;>
    simp [E, M, Matrix.mulVec, dotProduct, Fin.sum_univ_two, cos_add, sin_add] <;>
    field_simp <;>
    first
    | ring1
    | linear_combination (-(cos θ₀ * sin (κ ε * φ))) * κ_sq h

/-- **The linearized tori solve the variational equation of the actual axis**,
`v' = 2ε S(φ) v` (the Jacobian of the field-line system at the axis, `fieldLineSystem_jacobian`). -/
theorem linTorus_hasDerivAt {ε : ℝ} (h : 4 * ε ^ 2 < 1) (θ₀ φ : ℝ) (i : Fin 2) :
    HasDerivAt (fun s => linTorus ε θ₀ s i) ((((2 * ε) • S φ) *ᵥ linTorus ε θ₀ φ) i) φ := by
  have hfun : (fun s => linTorus ε θ₀ s i) =
      fun s => Φ ε s i 0 * linTorus ε θ₀ 0 0 + Φ ε s i 1 * linTorus ε θ₀ 0 1 := by
    funext s
    rw [linTorus_eq_Φ h θ₀ s]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hfun]
  have hd := (((Φ_solves h φ).1 i 0).mul_const (linTorus ε θ₀ 0 0)).add
    (((Φ_solves h φ).1 i 1).mul_const (linTorus ε θ₀ 0 1))
  convert hd using 1
  rw [linTorus_eq_Φ h θ₀ φ, Matrix.mulVec_mulVec]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **The first-order `‖B‖` of the actual field on the linearized torus**: the derivative of
`‖B‖` at `axis φ` in the direction of the torus point `v(θ₀, φ)` (embedded in the poloidal
plane). -/
@[expose] def firstOrderNormB (ε θ₀ φ : ℝ) : ℝ :=
  fderiv ℝ (fun y => ‖field ε y‖) (axis φ) (poloidalMap φ (linTorus ε θ₀ φ))

/-- `firstOrderNormB` is the first-order coefficient in `r`:
`‖B(axis φ + r v)‖ = 1 + r · firstOrderNormB + o(r)`. -/
theorem firstOrderNormB_hasDerivAt (ε θ₀ φ : ℝ) :
    HasDerivAt (fun r : ℝ => ‖field ε (axis φ + r • poloidalMap φ (linTorus ε θ₀ φ))‖)
      (firstOrderNormB ε θ₀ φ) 0 := by
  set u := poloidalMap φ (linTorus ε θ₀ φ)
  have hp : HasDerivAt (fun r : ℝ => axis φ + r • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add (axis φ)
  have hN := normField_hasFDerivAt_axis ε φ
  have := hN.comp_hasDerivAt_of_eq 0 hp (by simp)
  rw [firstOrderNormB, hN.fderiv]
  exact this

/-- `κ_N` for `N = 2` is the `κ` of `RationalStellaratorAxis`. -/
theorem kappaN_two (ε : ℝ) : kappaN 2 ε = κ ε := by
  rw [kappaN, κ]; norm_num

/-- `ι₀` for `N = 2` is `iota0`. -/
theorem iotaN_two (ε : ℝ) : iotaN 2 ε = iota0 ε := by
  rw [iotaN, iota0, kappaN_two]; norm_num

/-- **The first-order `‖B‖` of the actual rational field, in straight-field-line angles, is the
rotating-ellipse expression** `b1 2 ε`: with `θ_s = ι₀ φ − θ₀` (the field line `θ₀ = const`
has `dθ_s/dφ = ι₀`), `firstOrderNormB ε (ι₀ φ − θ_s) φ = b1 2 ε θ_s φ`. -/
theorem firstOrderNormB_eq_b1 (ε θs φ : ℝ) :
    firstOrderNormB ε (iota0 ε * φ - θs) φ = b1 2 ε θs φ := by
  rw [firstOrderNormB, (normField_hasFDerivAt_axis ε φ).fderiv]
  have hth : iota0 ε * φ - θs + κ ε * φ = φ - θs := by rw [iota0]; ring
  simp only [_root_.neg_apply, innerSL_apply_apply, linTorus, hth]
  set b := φ - θs with hb
  have h2 : 2 * φ - θs = φ + b := by rw [hb]; ring
  have h1 : θs = φ - b := by rw [hb]; ring
  simp only [b1, qaPart, nonQAPart, qaCos, nonQACos, kappaN_two, h2]
  rw [h1]
  simp [poloidalMap, eR, eZ, rot, PiLp.inner_apply,
    Fin.sum_univ_three, cos_add, sin_add, cos_sub, sin_sub]
  have hcs := cos_sq_add_sin_sq φ
  linear_combination (-(cos b * cos φ + 2 * ε * cos b * sin φ + κ ε * sin b * sin φ)) * hcs

/-- **The rational stellarator is not quasisymmetric at first order, for any helicity.** For
`ε ≠ 0`, `4ε² < 1` (so `ι₀ = 1 − √(1 − 4ε²) ≠ 0`), the first-order `‖B‖` of
`RationalStellarator.field ε` on its linearized tori, as a function of the straight-field-line
angles `(θ_s, φ)`, is not a function of `Mθ_s − 2Kφ` for any `(M, K) ≠ (0, 0)`. -/
theorem rationalStellarator_firstOrder_not_QS {ε : ℝ} (hε : ε ≠ 0) (h : 4 * ε ^ 2 < 1)
    {M K : ℝ} (hMK : M ≠ 0 ∨ K ≠ 0) :
    ¬ IsQuasiSymmetric (fun θs φ => firstOrderNormB ε (iota0 ε * φ - θs) φ) 2 M K := by
  have he : (fun θs φ => firstOrderNormB ε (iota0 ε * φ - θs) φ) = b1 2 ε := by
    funext θs φ; exact firstOrderNormB_eq_b1 ε θs φ
  have h16 : 16 * ε ^ 2 ≤ (2 : ℝ) ^ 2 := by nlinarith
  rw [he]
  exact b1_not_quasiSymmetric (by norm_num) h16
    (fun h0 => hε ((iotaN_eq_zero_iff (by norm_num) h16).mp h0)) hMK

/-- **The QA defect of the actual rational field at first order.** For `4ε² < 1`: the
first-order `‖B‖` in `(θ_s, φ)` differs from its QA part by at most `√(2ι₀)/2`, no function of
`θ_s` alone does better, and the non-QA fraction is `√(ι₀/2)`. -/
theorem rationalStellarator_firstOrder_QA_defect {ε : ℝ} (h : 4 * ε ^ 2 < 1) :
    (∀ θs φ, |firstOrderNormB ε (iota0 ε * φ - θs) φ - qaPart 2 ε θs| ≤ nonQAAmp 2 ε) ∧
    (∀ f : ℝ → ℝ, ∃ θs φ, nonQAAmp 2 ε ≤ |firstOrderNormB ε (iota0 ε * φ - θs) φ - f θs|) ∧
    nonQAAmp 2 ε = √(2 * iota0 ε) / 2 ∧
    nonQAAmp 2 ε / √(qaAmp 2 ε ^ 2 + nonQAAmp 2 ε ^ 2) = √(iota0 ε / 2) := by
  have h16 : 16 * ε ^ 2 ≤ (2 : ℝ) ^ 2 := by nlinarith
  obtain ⟨-, h2, h3, h4, h5, -⟩ := rotatingEllipse_firstOrder_QA_defect (by norm_num) h16
  refine ⟨fun θs φ => by rw [firstOrderNormB_eq_b1]; exact h2 θs φ,
    fun f => by simpa only [firstOrderNormB_eq_b1] using h3 f, by rw [← iotaN_two]; exact h4,
    by rw [← iotaN_two]; exact h5⟩

/-- **Numeric instance (`ε = 1/4`, the rational stellarator).** `ι₀ = 1 − √3/2` and the non-QA
fraction `√(ι₀/2)` lies in `(0.2588, 0.2589)` (N-30 §3.2 measures 0.259 at `r = 0.05`). -/
theorem nonQA_fraction_quarter :
    iotaN 2 (1 / 4) = 1 - √3 / 2 ∧
      (2588 / 10000 : ℝ) < √(iotaN 2 (1 / 4) / 2) ∧ √(iotaN 2 (1 / 4) / 2) < 2589 / 10000 := by
  have hι : iotaN 2 (1 / 4) = 1 - √3 / 2 := by rw [iotaN_two, iota0_quarter]
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 ≤ √3 := Real.sqrt_nonneg 3
  have hlo : √3 < 173209 / 100000 := by nlinarith
  have hhi : 1732 / 1000 < √3 := by nlinarith
  refine ⟨hι, ?_, ?_⟩
  · rw [Real.lt_sqrt (by norm_num), hι]; linarith
  · rw [Real.sqrt_lt' (by norm_num), hι]; linarith

end Field

end PlasmaLean.Design.RationalStellaratorQAObstruction
