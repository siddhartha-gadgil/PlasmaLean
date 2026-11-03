/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Analysis.Normed.Order.Lattice

/-!
# Prototype: the algebra of the vacuum Boozer angles on an invariant torus (N-34)

**Prototype, not imported by `PlasmaLean.lean`.** Design study
`notes/theory/dommaschk-qs-defect.md` (N-34), §2. It checks that the pointwise algebra behind the
proposed contract-level quasi-axisymmetry defect closes in Lean with short proofs, and that the
global invertibility of the angle change reduces to a one-dimensional monotonicity lemma.

Setting. On an invariant torus `K(θ, φ)` with frequency `(ι, 1)` (`𝓛 = ∂_φ + ι ∂_θ`) of a vacuum
field `B = ∇Φ`, `Φ = φ + V`, put `v = V ∘ K`, `φ_B = φ + v`, `θ_B = θ + ι v`. With
`v_θ, v_φ` the partial derivatives and `J = 1 + v_φ + ι v_θ` (the Boozer Jacobian), the torus
vector `X = (−ι v_φ, 1 + ι v_θ)/J` is `∂_{φ_B}` at fixed `θ_B`:

* `boozerX_thetaB`, `boozerX_phiB`: `X θ_B = 0`, `X φ_B = 1`;
* `boozerX_apply`: `X f = (1 + ι v_θ) 𝓛f / J − ι ∂_θ f` (the formula of the defect);
* `boozerX_qa`: a function of `θ_B` alone has `X f = 0` (exact QA has zero defect);
* `boozerVec_eq`: pushed forward to space, `X = B/|B|² − ι (∂_θK − (b·∂_θK) b)` when
  `𝓛K = B/B^φ` (invariance) and `v_θ = ⟪B, ∂_θK⟫`, `J = ⟪B, 𝓛K⟫` (because `B = ∇Φ`);
* `bijective_of_strictMono_bdd`: along each field line (fixed `α = θ − ιφ`) the map
  `φ ↦ φ_B` is strictly increasing (`J > 0`) and `φ_B − φ` is bounded, hence bijective;
* `coeff_sq_le`: the scalar step of the Wirtinger bound (`c(g) = i q N c(f)`, `q ≠ 0`).
-/

public section
noncomputable section
namespace PlasmaLean.Design.DommaschkQSProto

open scoped RealInnerProductSpace

/-- The `θ`-component of `∂_{φ_B}|_{θ_B}` in the KAM chart. -/
@[expose] def bx1 (ι vθ vφ : ℝ) : ℝ := -(ι * vφ) / (1 + vφ + ι * vθ)

/-- The `φ`-component of `∂_{φ_B}|_{θ_B}` in the KAM chart. -/
@[expose] def bx2 (ι vθ vφ : ℝ) : ℝ := (1 + ι * vθ) / (1 + vφ + ι * vθ)

/-- `X θ_B = 0`: the differential of `θ_B = θ + ι v` is `(1 + ι v_θ, ι v_φ)`. -/
theorem boozerX_thetaB {ι vθ vφ : ℝ} (hJ : 1 + vφ + ι * vθ ≠ 0) :
    (1 + ι * vθ) * bx1 ι vθ vφ + ι * vφ * bx2 ι vθ vφ = 0 := by
  unfold bx1 bx2; field_simp; ring

/-- `X φ_B = 1`: the differential of `φ_B = φ + v` is `(v_θ, 1 + v_φ)`. -/
theorem boozerX_phiB {ι vθ vφ : ℝ} (hJ : 1 + vφ + ι * vθ ≠ 0) :
    vθ * bx1 ι vθ vφ + (1 + vφ) * bx2 ι vθ vφ = 1 := by
  unfold bx1 bx2
  rw [mul_div_assoc', mul_div_assoc', ← add_div, div_eq_one_iff_eq hJ]; ring

/-- The defect formula: `X f = (1 + ι v_θ) 𝓛f / J − ι ∂_θ f`, with `𝓛f = f_φ + ι f_θ`. -/
theorem boozerX_apply {ι vθ vφ fθ fφ : ℝ} (hJ : 1 + vφ + ι * vθ ≠ 0) :
    bx1 ι vθ vφ * fθ + bx2 ι vθ vφ * fφ =
      (1 + ι * vθ) * (fφ + ι * fθ) / (1 + vφ + ι * vθ) - ι * fθ := by
  unfold bx1 bx2; field_simp; ring

/-- Exact QA on the torus has zero defect: if `f = F ∘ θ_B`, the chain rule gives
`f_θ = F' (1 + ι v_θ)` and `f_φ = F' ι v_φ`, and then `X f = 0`. -/
theorem boozerX_qa {ι vθ vφ F' : ℝ} (hJ : 1 + vφ + ι * vθ ≠ 0) :
    bx1 ι vθ vφ * (F' * (1 + ι * vθ)) + bx2 ι vθ vφ * (F' * (ι * vφ)) = 0 := by
  unfold bx1 bx2; field_simp; ring

/-- The pushed-forward Boozer vector: with `𝓛K = β⁻¹ B` (`β = B^φ ≠ 0`), `a = ⟪B, ∂_θK⟫`,
`J = ⟪B, 𝓛K⟫` and `v_φ = J − 1 − ι a`, the tangent vector `X¹ ∂_θK + X² ∂_φK` equals
`B/|B|² − ι (∂_θK − (⟪B, ∂_θK⟫/|B|²) B)`. -/
theorem boozerVec_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {B Kθ Kφ : E} {ι β : ℝ} (hβ : β ≠ 0) (hB : ‖B‖ ≠ 0)
    (hinv : Kφ + ι • Kθ = β⁻¹ • B) :
    let a := ⟪B, Kθ⟫
    let J := ⟪B, Kφ + ι • Kθ⟫
    bx1 ι a (J - 1 - ι * a) • Kθ + bx2 ι a (J - 1 - ι * a) • Kφ =
      (‖B‖ ^ 2)⁻¹ • B - ι • (Kθ - (a / ‖B‖ ^ 2) • B) := by
  intro a J
  have hJ : J = β⁻¹ * ‖B‖ ^ 2 := by
    simp only [J, hinv, inner_smul_right, real_inner_self_eq_norm_sq]
  have hJ0 : 1 + (J - 1 - ι * a) + ι * a ≠ 0 := by
    rw [show 1 + (J - 1 - ι * a) + ι * a = J by ring, hJ]
    exact mul_ne_zero (inv_ne_zero hβ) (pow_ne_zero 2 hB)
  have hKφ : Kφ = β⁻¹ • B - ι • Kθ := by rw [← hinv]; abel
  rw [hKφ]
  have e1 : bx1 ι a (J - 1 - ι * a) - ι * bx2 ι a (J - 1 - ι * a) = -ι := by
    unfold bx1 bx2; field_simp; ring
  have e2 : bx2 ι a (J - 1 - ι * a) * β⁻¹ = (‖B‖ ^ 2)⁻¹ + ι * (a / ‖B‖ ^ 2) := by
    unfold bx2
    rw [show 1 + (J - 1 - ι * a) + ι * a = J by ring, hJ]
    field_simp
  calc bx1 ι a (J - 1 - ι * a) • Kθ + bx2 ι a (J - 1 - ι * a) • (β⁻¹ • B - ι • Kθ)
      = (bx1 ι a (J - 1 - ι * a) - ι * bx2 ι a (J - 1 - ι * a)) • Kθ +
          (bx2 ι a (J - 1 - ι * a) * β⁻¹) • B := by
        simp only [smul_sub, smul_smul, sub_smul]; abel_nf; simp only [mul_comm]
    _ = _ := by rw [e1, e2, add_smul, smul_sub, smul_smul, neg_smul]; abel

/-- **Global invertibility along a field line.** A continuous strictly increasing `f : ℝ → ℝ`
with `|f x − x| ≤ C` is bijective (`f = (φ ↦ φ_B)` at fixed field-line label; `J > 0` gives
strict monotonicity, periodicity of `v` gives the bound). -/
theorem bijective_of_strictMono_bdd {f : ℝ → ℝ} {C : ℝ} (hc : Continuous f)
    (hm : StrictMono f) (hb : ∀ x, |f x - x| ≤ C) : Function.Bijective f := by
  refine ⟨hm.injective, hc.surjective ?_ ?_⟩
  · refine Filter.tendsto_atTop_mono (fun x => ?_) (Filter.tendsto_atTop_add_const_right _ (-C)
      Filter.tendsto_id)
    have := (abs_le.1 (hb x)).1; simp only [id]; linarith
  · refine Filter.tendsto_atBot_mono (fun x => ?_) (Filter.tendsto_atBot_add_const_right _ C
      Filter.tendsto_id)
    have := (abs_le.1 (hb x)).2; simp only [id]; linarith

/-- The scalar Wirtinger step: if `|c_g| = |q| N |c_f|` with an integer `q ≠ 0` and `N > 0`,
then `|c_f|² ≤ |c_g|²/N²`. -/
theorem coeff_sq_le {cf cg N : ℝ} {q : ℤ} (hq : q ≠ 0) (hN : 0 < N)
    (h : |cg| = |(q : ℝ)| * N * |cf|) : cf ^ 2 ≤ cg ^ 2 / N ^ 2 := by
  have hq1 : (1 : ℝ) ≤ |(q : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hq
  rw [le_div_iff₀ (by positivity), ← sq_abs cg, h, ← sq_abs cf]
  calc |cf| ^ 2 * N ^ 2 = 1 * (N * |cf|) ^ 2 := by ring
    _ ≤ |(q : ℝ)| ^ 2 * (N * |cf|) ^ 2 := by gcongr; exact one_le_pow₀ hq1
    _ = (|(q : ℝ)| * N * |cf|) ^ 2 := by ring

/-! ## Sanity -/

/-- Degenerate case: with `v = 0` (`φ_B = φ`, `θ_B = θ`), `X = ∂_φ`. -/
theorem boozerX_trivial (ι : ℝ) : bx1 ι 0 0 = 0 ∧ bx2 ι 0 0 = 1 := by
  simp [bx1, bx2]

/-- Concrete instance: `ι = −1/4`, `v_θ = 1/10`, `v_φ = 1/20`: `J = 41/40`, `X = (1/82, 39/41)`. -/
theorem boozerX_concrete :
    bx1 (-1/4) (1/10) (1/20) = 1/82 ∧ bx2 (-1/4) (1/10) (1/20) = 78/82 := by
  norm_num [bx1, bx2]

/-- Rejected fixture for the bound hypothesis of `bijective_of_strictMono_bdd`: the strictly
increasing map `x ↦ 2x` is not within distance `1` of the identity. -/
theorem not_bdd_double : ¬ ∀ x : ℝ, |2 * x - x| ≤ 1 := by
  intro h; have := h 2; norm_num [abs_of_pos] at this

end PlasmaLean.Design.DommaschkQSProto
