/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2Ballooning
public import PlasmaLean.Theory.Stability.BallooningSecular

/-!
# Family-2 ballooning: the secular part of the certificate is exact

For Landreman's family 2 (`ε = 1/4`, `S = 4`, every `λ > 0`), the surface certificate of
`LandremanFamily2Ballooning.family2_stable_of_cert` must satisfy
`DΦ(B, d) + Φ²/P ≤ q₀ + s q₁` for ALL `s ∈ ℝ`. Letting `s → ±∞` forces the coefficient of `s`
in `Φ` to solve the magnetic differential equation `B · ∇a = q₁` exactly. This module supplies
that exact solution from the actual field and removes `q₁` from the certificate condition.

* `jpar2`: the actual parallel current `J∥ = ⟪curl B, B⟫/|B|²` (`curl` of the actual Fréchet
  derivative `fieldDeriv`), and `jparD2`, its derivative (built from the actual second
  derivative `fderiv ℝ (fderiv ℝ field)`).
* `family2_jpar_hasFDerivAt`, `family2_jpar_transport`: on the shell, `J∥` is differentiable
  and `B · ∇J∥ = −(2/λ²) ⟪B × ∇ψ, κ⟫/|B|² = −q₁`. Proof: the general
  `BallooningSecular.jpar_transport` (from `C²`, `∇ · B = 0`, the force balance
  `(∇ × B) × B = −∇ψ/λ²` on the open set `𝒰` and the symmetric Hessian of `ψ`).
* `family2_stable_of_secular_cert`: with `Φ = (c₀ − J∥) s + F(x, s)`, ballooning stability of
  a field line for every eikonal family follows from the `q₁`-free inequality
  `DF(B, d) + d (c₀ − J∥) + ((c₀ − J∥) s + F)²/P ≤ (2/λ²) ⟪∇ψ, κ⟫/|∇ψ|²`.

The remaining certificate `F` (and `c₀`) is the object of the untrusted search in
`scripts/family2_ballooning_cert/`; it is not supplied here, so no stability theorem for
family 2 is claimed.
-/

open scoped RealInnerProductSpace

public section
noncomputable section

namespace PlasmaLean.Design.LandremanFamily2BallooningSecular

open Set Filter Topology WithLp
open PlasmaLean.Fields PlasmaLean.Stability PlasmaLean.Stability.BallooningReduction
open PlasmaLean.Stability.BallooningSurface PlasmaLean.Stability.BallooningSecular
open PlasmaLean.Design.LandremanFamily2 PlasmaLean.Design.LandremanFamily2Surface
open PlasmaLean.Design.LandremanFamily2Coords PlasmaLean.Design.LandremanFamily2Ballooning

/-- The actual parallel current `J∥ = ⟪curl B, B⟫/|B|²` of family 2. -/
@[expose] def jpar2 (lam : ℝ) (x : Space) : ℝ :=
  jparOf (fieldDeriv (1 / 4) 4 lam x) (field (1 / 4) 4 lam x)

/-- The derivative of `J∥` (from the actual second derivative of the field). -/
@[expose] def jparD2 (lam : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  jparDeriv (fieldDeriv (1 / 4) 4 lam x) (fderiv ℝ (fderiv ℝ (field (1 / 4) 4 lam)) x)
    (field (1 / 4) 4 lam x)

section Smooth
variable {lam : ℝ} {x : Space}

/-- On `𝒰` the actual derivative `fieldDeriv` is the Fréchet derivative of the field near
`x`. -/
theorem fieldDeriv_eventuallyEq (hx : x ∈ U (1 / 4)) :
    fderiv ℝ (field (1 / 4) 4 lam) =ᶠ[𝓝 x] fieldDeriv (1 / 4) 4 lam := by
  filter_upwards [(isOpen_U (1 / 4)).mem_nhds hx] with y hy
  exact (field_hasFDerivAt (1 / 4) 4 lam hy).fderiv

/-- `fieldDeriv` is differentiable on `𝒰`, with derivative the second derivative of the
field. -/
theorem hasFDerivAt_fieldDeriv (hx : x ∈ U (1 / 4)) :
    HasFDerivAt (fieldDeriv (1 / 4) 4 lam) (fderiv ℝ (fderiv ℝ (field (1 / 4) 4 lam)) x) x := by
  have hcd : ContDiffAt ℝ 2 (field (1 / 4) 4 lam) x := contDiffAt_field 4 lam hx
  have hd : HasFDerivAt (fderiv ℝ (field (1 / 4) 4 lam))
      (fderiv ℝ (fderiv ℝ (field (1 / 4) 4 lam)) x) x :=
    ((hcd.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  exact hd.congr_of_eventuallyEq (fieldDeriv_eventuallyEq hx).symm

/-- The second derivative of the field is symmetric on `𝒰`. -/
theorem fieldDeriv2_symm (hx : x ∈ U (1 / 4)) (u v : Space) :
    fderiv ℝ (fderiv ℝ (field (1 / 4) 4 lam)) x u v =
      fderiv ℝ (fderiv ℝ (field (1 / 4) 4 lam)) x v u :=
  (contDiffAt_field (n := 2) 4 lam hx).isSymmSndFDerivAt (by simp) u v

/-- The second derivative of the field is continuous on `𝒰`. -/
theorem continuousOn_fieldDeriv2 :
    ContinuousOn (fderiv ℝ (fderiv ℝ (field (1 / 4) 4 lam))) (U (1 / 4)) := by
  have hcd : ContDiffOn ℝ 2 (field (1 / 4) 4 lam) (U (1 / 4)) :=
    fun _ hy => (contDiffAt_field 4 lam hy).contDiffWithinAt
  exact (hcd.fderiv_of_isOpen (isOpen_U _) (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen
    (isOpen_U _) le_rfl

end Smooth

/-- **`J∥` is differentiable on the shell** (`λ > 0`), with derivative `jparD2`. -/
theorem family2_jpar_hasFDerivAt {lam : ℝ} (hl : 0 < lam) {x : Space}
    (hx : x ∈ shell lam (19 / 20)) : HasFDerivAt (jpar2 lam) (jparD2 lam x) x :=
  hasFDerivAt_jpar (field_hasFDerivAt (1 / 4) 4 lam hx.1.1) (hasFDerivAt_fieldDeriv hx.1.1)
    (field_ne_of_shell hl hx)

/-- **The secular transport identity of family 2**: on the shell,
`B · ∇J∥ = 2μ ⟪B × ∇ψ, κ⟫/|B|²` with `μ = −1/λ²`, i.e. `B · ∇J∥ = −q₁` for the secular
coefficient `q₁` of the ballooning drive. -/
theorem family2_jpar_transport {lam : ℝ} (hl : 0 < lam) {x : Space}
    (hx : x ∈ shell lam (19 / 20)) :
    jparD2 lam x (field (1 / 4) 4 lam x) =
      2 * (-(lam ^ 2)⁻¹) * ⟪cross (field (1 / 4) 4 lam x) (gradPsi (1 / 4) 4 lam x),
        kappa2 (1 / 4) 4 lam x⟫ / ‖field (1 / 4) 4 lam x‖ ^ 2 := by
  have hU : x ∈ U (1 / 4) := hx.1.1
  obtain ⟨G, hG, hGs⟩ := hasFDerivAt_grad_symm ((isOpen_U (1 / 4)).mem_nhds hU)
    (contDiffAt_psi (n := 2) 4 lam hU) (fun y hy => psi_hasFDerivAt (1 / 4) 4 lam hy)
  have htr : divergence (fieldDeriv (1 / 4) 4 lam x) = 0 := by
    have := field_divergence_free (S := 4) hl.ne' hU
    rwa [(field_hasFDerivAt (1 / 4) 4 lam hU).fderiv] at this
  exact jpar_transport ((isOpen_U (1 / 4)).mem_nhds hU) (field_hasFDerivAt (1 / 4) 4 lam hU)
    (hasFDerivAt_fieldDeriv hU) (fieldDeriv2_symm hU) hG hGs
    (fun y hy => transport_key hl.ne' hy) htr (field_ne_of_shell hl hx)

/-- Along a field line in the shell, `t ↦ jparD2 (X t)` is continuous. -/
theorem cont_jparD2 {lam : ℝ} (hl : 0 < lam) {X : ℝ → Space} (L : FieldLine lam X) :
    Continuous fun t => jparD2 lam (X t) := by
  have hB := L.cont_B
  have hM := L.cont_M
  have hM2 : Continuous fun t => fderiv ℝ (fderiv ℝ (field (1 / 4) 4 lam)) (X t) :=
    continuous_iff_continuousAt.mpr fun t =>
      (continuousOn_fieldDeriv2.continuousAt ((isOpen_U _).mem_nhds (L.shell t).1.1)).comp
        L.continuous.continuousAt
  have hn : ∀ t, ‖field (1 / 4) 4 lam (X t)‖ ^ 2 ≠ 0 := fun t =>
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (field_ne_of_shell hl (L.shell t)))
  have hiB : Continuous fun t => innerSL ℝ (field (1 / 4) 4 lam (X t)) :=
    (innerSL ℝ).continuous.comp hB
  have hcM : Continuous fun t => curl (fieldDeriv (1 / 4) 4 lam (X t)) :=
    curlCLM.continuous.comp hM
  unfold jparD2 jparDeriv
  refine (((hB.norm.pow 2).inv₀ hn).smul ((hiB.clm_comp (continuous_const.clm_comp hM2)).add
    (((innerSL ℝ).continuous.comp hcM).clm_comp hM))).sub ?_
  refine (((hcM.inner hB).mul continuous_const).div ((hB.norm.pow 2).pow 2) fun t =>
    pow_ne_zero 2 (hn t)).smul (hiB.clm_comp hM)

/-- **Reduction of family-2 ballooning to a `q₁`-free surface inequality.** For a field line
`X` in the shell, a secular variable `σ' = d(X)`, a constant `c₀` and a `C¹` function
`F(x, s)` with derivative `DF` such that, at the points of the line and for all `s`,

  `DF(x, s)(B, d) + d (c₀ − J∥) + ((c₀ − J∥) s + F)²/P ≤ (2/λ²) ⟪∇ψ, κ⟫/|∇ψ|²`,

the line is ballooning stable for EVERY eikonal family `c` (the supplied reduction). The
certificate of `family2_stable_of_cert` is `Φ = (c₀ − J∥) s + F`. -/
theorem family2_stable_of_secular_cert {lam : ℝ} (hl : 0 < lam) {X : ℝ → Space}
    (L : FieldLine lam X) {σ : ℝ → ℝ} (hσ : ∀ t, HasDerivAt σ (shear2 (1 / 4) 4 lam (X t)) t)
    (c₀ : ℝ) {F : Space × ℝ → ℝ} {DF : Space × ℝ → (Space × ℝ →L[ℝ] ℝ)}
    (hF : ∀ t s, HasFDerivAt F (DF (X t, s)) (X t, s))
    (hDF : Continuous fun p : ℝ × ℝ => DF (X p.1, p.2))
    (hcert : ∀ t s, DF (X t, s) (field (1 / 4) 4 lam (X t), shear2 (1 / 4) 4 lam (X t)) +
      shear2 (1 / 4) 4 lam (X t) * (c₀ - jpar2 lam (X t)) +
      ((c₀ - jpar2 lam (X t)) * s + F (X t, s)) ^ 2 /
        eikP (field (1 / 4) 4 lam (X t)) (gradPsi (1 / 4) 4 lam (X t)) s ≤
      -(2 * (-(lam ^ 2)⁻¹) * ⟪gradPsi (1 / 4) 4 lam (X t), kappa2 (1 / 4) 4 lam (X t)⟫) /
        ‖gradPsi (1 / 4) 4 lam (X t)‖ ^ 2)
    (c : ℝ) : (family2Line hl L hσ c).Stable :=
  eikLine_stable_of_secularCert L.deriv _ _ _ L.cont_B L.cont_g (L.cont_kappa hl)
    (L.cont_shear hl) hσ (fun t => family2_jpar_hasFDerivAt hl (L.shell t))
    (cont_jparD2 hl L) (fun t => family2_jpar_transport hl (L.shell t)) c₀ hF hDF hcert c

/-! ## Sanity checks -/

/-- Special case (closed form): on the surface `ψ = k²/2`, `J∥ = λ + BD/Bsq`, the closed forms
of `LandremanFamily2Surface` (so `J∥ − λ` is `O(1/λ)`, and the secular coefficient
`c₀ − J∥` is available to an interval checker without derivatives). -/
theorem jpar2_surfPt {lam k χ ζ : ℝ} (hl : 0 < lam) (hk0 : 0 < k) (hk1 : k ≤ 19 / 20) :
    jpar2 lam (surfPt (1 / 4) 4 lam k χ ζ) =
      lam + BD (1 / 4) 4 lam k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) /
        Bsq (1 / 4) 4 lam k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) := by
  have hU := surfPt_mem_U (lam := lam) (k := k) (χ := χ) (ζ := ζ)
  have hX := inner_field_Xi_surfPt (χ := χ) (ζ := ζ) hl.ne' hk0 hk1 one_ne_zero 0
  have hc : current 1 (1 / 4) 4 lam (surfPt (1 / 4) 4 lam k χ ζ) =
      curl (fieldDeriv (1 / 4) 4 lam (surfPt (1 / 4) 4 lam k χ ζ)) := by
    rw [current, (field_hasFDerivAt (1 / 4) 4 lam hU).fderiv, inv_one, one_smul]
  rw [one_smul, zero_smul, sub_zero, hc, sub_zero, real_inner_comm] at hX
  have hp := Bsq_pos (ε := 1 / 4) (S := 4) (lam := lam) (s1 := Real.sin χ) (c1 := Real.cos χ)
    (s2 := Real.sin (2 * ζ)) (by norm_num) (Real.abs_cos_le_one (2 * ζ)) (k_sq_lt_one hk0 hk1)
  rw [jpar2, jparOf, hX, normSq_field_surfPt hl.ne' hk0 hk1]
  field_simp

end PlasmaLean.Design.LandremanFamily2BallooningSecular
