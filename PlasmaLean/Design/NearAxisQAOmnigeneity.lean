/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedBounce
public import PlasmaLean.Theory.Kinetic.Omnigeneity

/-!
# Omnigeneity of the reactor-scale near-axis QA models (Q-23 applied)

Research note: `notes/theory/omnigeneity-bridge.md` (N-29). Applies
`Theory/Kinetic/Omnigeneity` to the near-axis QA family `qaField b₁` of
`Design/NearAxisQATrappedBounce` (truncated second-order near-axis model, inserted in the vacuum
Boozer guiding-centre model; both are supplied models, see `Design/NearAxisQA`).

* `exactQA_omnigenousOn`: the exactly quasi-axisymmetric member `exactQA` (`b₁ = 0`) is
  **omnigenous** on every region `0 < ψ ≤ c` (concrete, non-constant instance of the exact
  theorem).
* `reactorQA_approxOmnigenousOn`: `reactorQA` (`b₁ = −4.3 × 10⁻⁴`) is approximately omnigenous on
  `0 < ψ ≤ ψ_a` with `κ = 2 ε_QS(a)/(B_min ι₀)`, `ε_QS(a) = 0.0024854 T`, `B_min = 4.93 T`,
  `ι₀ = 0.422`.
* `reactorQA_alpha_bounce_drift`: for 3.5 MeV alphas (any `μ ≥ 0`), every trapped bounce in
  `0 < ψ ≤ ψ_a` has `|ψ(τ) − ψ(0)| ≤ 4182 τ` (T m², `τ` in s) and bounce-averaged radial drift
  `|Δψ/τ| ≤ 4182 T m²/s`.

The bound is the worst-case (constant-sign forcing) bound, linear in `ε_QS` and in the bounce
time; it does not use the oscillation of the `sin 2φ` defect along the banana, so it is far from
the true bounce-averaged drift. Its role is the exact/quantitative structure, not a transport
estimate.
-/
public section
noncomputable section
namespace PlasmaLean.Design.NearAxisQAOmnigeneity
open PlasmaLean.Kinetic.Boozer PlasmaLean.Design.NearAxisQA
  PlasmaLean.Design.NearAxisQATrappedBounce Real Set

/-- **`exactQA` is omnigenous** on every region `0 < ψ ≤ c`: exact quasi-axisymmetry
(`∂_φB ≡ 0`) and `ψ_p = 0.422 ψ` injective. The existence of a trapped bounce in `exactQA` is not
proved here, so this may hold vacuously; definitional non-vacuity of `OmnigenousOn` is the
`driftMirror` fixture. -/
theorem exactQA_omnigenousOn (c : ℝ) : OmnigenousOn exactQA c := by
  refine omnigenousOn_of_exactQS (N := 0) (M := 1) (by rw [exactQA, qaField_G]; norm_num)
    (fun x θ φ _ _ => by simp [symmetryDefect, exactQA_Bφ]) ?_
  intro x _ y _ hxy
  have hp : ∀ z, exactQA.ψp z = 211 / 500 * z := fun _ => rfl
  simp only [hp] at hxy
  linarith

/-- The symmetry defect of `reactorQA` is at most `ε_QS(a) = 0.0024854 T` on `0 < ψ ≤ ψ_a`. -/
theorem reactorQA_defect_le' {x θ φ : ℝ} (hx : 0 < x) (hxc : x ≤ psiEdge) :
    |symmetryDefect reactorQA 0 1 x θ φ| ≤ 0.0024854 := by
  have := nearAxis_symmetryDefect_le (η := -7 / 100) (b₀ := -137 / 10000)
    (b₁ := -43 / 100000) (B₂c := 33 / 2000) (ι₀ := 211 / 500) (G := 581 / 10) (θ := θ)
    (φ := φ) (by norm_num : (0 : ℝ) < 57 / 10) hx.le (radius_le_edge hxc)
  refine this.trans (le_of_eq ?_)
  norm_num [abs_of_neg]

/-- QA twist of `reactorQA` on `(0, ψ_a]` with `ι_min = ι₀ = 211/500`. -/
theorem reactorQA_twist : TwistOn reactorQA 0 1 psiEdge (211 / 500) :=
  twistOn_qa_of_iota_ge fun _ _ => le_rfl

/-- **`reactorQA` is approximately omnigenous** on `0 < ψ ≤ ψ_a`, with
`κ = 2 · 0.0024854/(4.93 · 0.422)`. -/
theorem reactorQA_approxOmnigenousOn :
    ApproxOmnigenousOn reactorQA psiEdge (2 * 0.0024854 / (4.93 * (211 / 500))) :=
  approxOmnigenousOn_of_defect_le (N := 0) (M := 1) (by rw [reactorQA_eq, qaField_G]; norm_num)
    (by norm_num) (by norm_num) (fun _ _ _ hx hxc => (reactorQA_B_bounds hx hxc).1)
    (fun _ _ _ hx hxc => reactorQA_defect_le' hx hxc) reactorQA_twist

/-- **3.5 MeV alphas in `reactorQA`**: every trapped bounce (any `μ ≥ 0`) in `0 < ψ ≤ ψ_a`
has `|ψ(τ) − ψ(0)| ≤ 4182 τ` and bounce-averaged radial drift `|Δψ/τ| ≤ 4182 T m²/s`. -/
theorem reactorQA_alpha_bounce_drift {μ τ : ℝ} {ψ θ φ ρ : ℝ → ℝ} (hμ : 0 ≤ μ)
    (hb : TrappedBounce reactorQA mα qα μ psiEdge ψ θ φ ρ τ)
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα) :
    |ψ τ - ψ 0| ≤ 4182 * τ ∧ |bounceAvgDrift ψ τ| ≤ 4182 := by
  have hτ := hb.bounce.pos
  have h := reactorQA_approxOmnigenousOn mα qα μ ψ θ φ ρ τ (by norm_num [mα])
    (by norm_num [qα]) hμ hb
  rw [hE] at h
  have hk : 2 * 0.0024854 / (4.93 * (211 / 500)) * (Eα / |qα|) ≤ (4182 : ℝ) := by
    norm_num [Eα, qα, abs_of_pos]
  have h1 : |ψ τ - ψ 0| ≤ 4182 * τ := h.trans (mul_le_mul_of_nonneg_right hk hτ.le)
  refine ⟨h1, ?_⟩
  rw [bounceAvgDrift, abs_div, abs_of_pos hτ, div_le_iff₀ hτ]
  exact h1

end PlasmaLean.Design.NearAxisQAOmnigeneity
