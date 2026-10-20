/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamTorusAExact
public import PlasmaLean.Design.RationalStellaratorForever
public import PlasmaLean.Theory.KAM.StripSmooth

/-!
# All-time field-line confinement in the rational stellarator (KAM route, K4)

**Main theorem** (`rationalStellarator_confined_forever`): there is a torus profile `ρ(θ, φ)`
with `0.077 ≤ ρ ≤ 0.19` (distance from the exact magnetic axis `R = 1, z = 0`) such that every
two-sided field line of `field (1/4)` starting on the axis or strictly inside the torus
`rt < ρ(θs, φs)` stays inside it — in particular within distance `0.19` of the axis — **for all
time**, forward and backward.

The torus is the exact invariant torus of rotational transform `ι = (75 + √5)/562` produced by
the KAM theorem (`torusA_exact`, `Design/KamTorusAExact`). It is turned into real functions
`R(θ, φ) = 1 + Re F_u(θ, ψ(φ))`, `z(θ, φ) = Re F_z(θ, ψ(φ))` (`Rof`, `Zof`; `ψ = 2φ − π/2`),
which are `C²` (`Theory/KAM/StripSmooth`), periodic, solve the flow-form invariance equation
pointwise (from `resR = resZ = 0` by evaluation), and are `10⁻¹⁰`-close to torus A in `C¹`
(`exactTorus`). The geometric half (`rationalStellarator_confined_forever_of_exact`,
`Design/RationalStellaratorForever`) converts such a torus into the trapping statement.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamNewton

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamTorusA WEll1Z2 Real
open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator

/-- The radius of the real torus of `u`: `R(θ, φ) = 1 + Re F_u(θ, ψ(φ))`. -/
def Rof (u : FA) (θ φ : ℝ) : ℝ := 1 + (eval u θ (psi φ)).re

/-- The height of the real torus of `z`: `z(θ, φ) = Re F_z(θ, ψ(φ))`. -/
def Zof (z : FA) (θ φ : ℝ) : ℝ := (eval z θ (psi φ)).re

/-- `phiOf (psi φ) = φ`. -/
theorem phiOf_psi (φ : ℝ) : phiOf (psi φ) = φ := by simp [phiOf, psi]

/-- A real element has real values. -/
theorem eval_ofReal_re {x : FA} (hx : IsReal x) (θ ψ : ℝ) :
    eval x θ ψ = ((eval x θ ψ).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [hx.eval_im]

/-- Values are bounded by the `ℓ¹` norm. -/
theorem norm_eval_le_of_Bd {x : FA} {ρ B : ℝ} (hρ : 0 ≤ ρ) (h : Bd ρ x B) (θ ψ : ℝ) :
    ‖eval x θ ψ‖ ≤ B := by
  have h0 := h.strip hρ
  obtain ⟨h1, h2⟩ := norm_fourierSum_le le_rfl h0.1 θ ψ
  exact h1.trans (h2.trans h0.2)

/-- `θ`-derivative of the real torus. -/
theorem hasDerivAt_Rof_θ {u : FA} (hu : Ana u) (θ φ : ℝ) :
    HasDerivAt (fun θ' => Rof u θ' φ) (eval (dTh u) θ (psi φ)).re θ := by
  have h := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_eval_θ hu θ (psi φ)))
  exact h.const_add 1

/-- `φ`-derivative of the real torus. -/
theorem hasDerivAt_Rof_φ {u : FA} (hu : Ana u) (θ φ : ℝ) :
    HasDerivAt (fun φ' => Rof u θ φ') (eval (dPh u) θ (psi φ)).re φ := by
  have hpsi : HasDerivAt psi 2 φ := by
    have h : HasDerivAt (fun x : ℝ => 2 * x - π / 2) (2 * 1) φ :=
      ((hasDerivAt_id φ).const_mul 2).sub_const (π / 2)
    rw [mul_one] at h; exact h
  have h1 := HasDerivAt.scomp φ (hasDerivAt_eval_ψ hu θ (psi φ)) hpsi
  have h2 := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt φ h1).const_add 1
  convert h2 using 1
  · funext x; rfl
  · rw [dPh_eq hu, eval_smul']
    simp [Complex.mul_re]

/-- `θ`-derivative of the real height. -/
theorem hasDerivAt_Zof_θ {z : FA} (hz : Ana z) (θ φ : ℝ) :
    HasDerivAt (fun θ' => Zof z θ' φ) (eval (dTh z) θ (psi φ)).re θ :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_eval_θ hz θ (psi φ))

/-- `φ`-derivative of the real height. -/
theorem hasDerivAt_Zof_φ {z : FA} (hz : Ana z) (θ φ : ℝ) :
    HasDerivAt (fun φ' => Zof z θ φ') (eval (dPh z) θ (psi φ)).re φ := by
  have hpsi : HasDerivAt psi 2 φ := by
    have h : HasDerivAt (fun x : ℝ => 2 * x - π / 2) (2 * 1) φ :=
      ((hasDerivAt_id φ).const_mul 2).sub_const (π / 2)
    rw [mul_one] at h; exact h
  have h1 := HasDerivAt.scomp φ (hasDerivAt_eval_ψ hz θ (psi φ)) hpsi
  have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt φ h1
  convert h2 using 1
  · funext x; rfl
  · rw [dPh_eq hz, eval_smul']
    simp [Complex.mul_re]

/-- `ψ(φ + π) = ψ(φ) + 2π`. -/
theorem psi_add_pi (φ : ℝ) : psi (φ + π) = psi φ + 2 * π := by simp [psi]; ring

/-- The smooth parametrization `(θ, φ) ↦ (θ, ψ(φ))`. -/
theorem contDiff_thpsi : ContDiff ℝ 2 (fun p : ℝ × ℝ => (p.1, psi p.2)) := by
  unfold psi; fun_prop

/-- Smoothness of the real torus. -/
theorem contDiff_Rof {u : FA} (hu : Ana u) : ContDiff ℝ 2 (fun p : ℝ × ℝ => Rof u p.1 p.2) := by
  have h := (Complex.reCLM.contDiff.comp ((contDiff_evalP 2 hu).comp contDiff_thpsi))
  exact contDiff_const.add h

/-- Smoothness of the real height. -/
theorem contDiff_Zof {z : FA} (hz : Ana z) : ContDiff ℝ 2 (fun p : ℝ × ℝ => Zof z p.1 p.2) :=
  Complex.reCLM.contDiff.comp ((contDiff_evalP 2 hz).comp contDiff_thpsi)

/-- The residual variables at a point of the exact torus. -/
theorem eval_xK_real {ι : ℝ} {u z : FA} (hu : Ana u) (hz : Ana z) (hur : IsReal u)
    (hzr : IsReal z) (θ φ : ℝ) :
    (fun j => eval (xK ι u z j) θ (psi φ)) =
      ptC (Rof u θ φ - 1) (Zof z θ φ) (Real.cos (2 * φ)) (Real.sin (2 * φ))
        (deriv (fun φ' => Rof u θ φ') φ + ι * deriv (fun θ' => Rof u θ' φ) θ)
        (deriv (fun φ' => Zof z θ φ') φ + ι * deriv (fun θ' => Zof z θ' φ) θ) := by
  rw [(hasDerivAt_Rof_θ hu θ φ).deriv, (hasDerivAt_Rof_φ hu θ φ).deriv,
    (hasDerivAt_Zof_θ hz θ φ).deriv, (hasDerivAt_Zof_φ hz θ φ).deriv]
  have hdPu : IsReal (dPh u) := by
    have := hur.dS 0 2; change IsReal (dS 0 2 u); norm_num at this; exact this
  have hdPz : IsReal (dPh z) := by
    have := hzr.dS 0 2; change IsReal (dS 0 2 z); norm_num at this; exact this
  have hLu : eval (Lt ι u) θ (psi φ) =
      (((eval (dPh u) θ (psi φ)).re + ι * (eval (dTh u) θ (psi φ)).re : ℝ) : ℂ) := by
    have h1 := (isReal_dTh hur).eval_im θ (psi φ)
    have h2 := hdPu.eval_im θ (psi φ)
    rw [Lt_eq ι hu, eval_add', eval_smul']
    apply Complex.ext
    · simp [h1]; ring
    · simp [h1, h2]
  have hLz : eval (Lt ι z) θ (psi φ) =
      (((eval (dPh z) θ (psi φ)).re + ι * (eval (dTh z) θ (psi φ)).re : ℝ) : ℂ) := by
    have h1 := (isReal_dTh hzr).eval_im θ (psi φ)
    have h2 := hdPz.eval_im θ (psi φ)
    rw [Lt_eq ι hz, eval_add', eval_smul']
    apply Complex.ext
    · simp [h1]; ring
    · simp [h1, h2]
  funext j
  fin_cases j
  · change eval u θ (psi φ) = ((Rof u θ φ - 1 : ℝ) : ℂ)
    rw [Rof, add_sub_cancel_left, ← eval_ofReal_re hur]
  · change eval z θ (psi φ) = ((Zof z θ φ : ℝ) : ℂ)
    rw [Zof, ← eval_ofReal_re hzr]
  · change eval cS θ (psi φ) = ((Real.cos (2 * φ) : ℝ) : ℂ)
    rw [eval_cS, cos_two_mul_eq]; push_cast; ring
  · change eval sS θ (psi φ) = ((Real.sin (2 * φ) : ℝ) : ℂ)
    rw [eval_sS, sin_two_mul_eq]
  · exact hLu
  · exact hLz

/-- **The exact KAM torus as a real `C²` torus** satisfying all the hypotheses of the geometric
theorem. -/
theorem exactTorus {u z : FA} (hu : Ana u) (hz : Ana z) (hur : IsReal u) (hzr : IsReal z)
    (hR : resR iota u z = 0) (hZ : resZ iota u z = 0) (hC : Close (rA / 7) iota u z u₀ z₀ μA) :
    ExactTorus (Rof u) (Zof z) := by
  have hr0 : (0 : ℝ) ≤ rA / 7 := by norm_num [rA]
  have hμ : μA ≤ 1 / 10 ^ 6 := by norm_num [μA]
  refine ⟨contDiff_Rof hu, contDiff_Zof hz, fun θ φ => ?_, fun θ φ => ?_, fun θ φ => ?_,
    fun θ φ => ?_, fun θ φ => ?_, fun θ φ => ?_, fun θ φ => ?_, fun θ φ => ?_, fun θ φ => ?_,
    fun θ φ => ?_⟩
  · simp only [Rof, eval_periodic_θ]
  · simp only [Zof, eval_periodic_θ]
  · simp only [Rof, psi_add_pi, eval_periodic_ψ]
  · simp only [Zof, psi_add_pi, eval_periodic_ψ]
  · have h := congrArg (fun x => eval x θ (psi φ)) hR
    simp only [resR, eval_zero'] at h
    rw [eval_polyExpr, eval_xK_real hu hz hur hzr, eval_resRp_ptC] at h
    have h' := Complex.ofReal_eq_zero.1 h
    rw [add_sub_cancel] at h'
    linarith
  · have h := congrArg (fun x => eval x θ (psi φ)) hZ
    simp only [resZ, eval_zero'] at h
    rw [eval_polyExpr, eval_xK_real hu hz hur hzr, eval_resZp_ptC] at h
    have h' := Complex.ofReal_eq_zero.1 h
    rw [add_sub_cancel] at h'
    linarith
  · have h1 := norm_eval_le_of_Bd hr0 hC.du θ (psi φ)
    rw [eval_sub', eval_u₀, phiOf_psi] at h1
    have h2 := (Complex.abs_re_le_norm _).trans h1
    simp only [Complex.sub_re, Complex.ofReal_re] at h2
    rw [Rof, show 1 + (eval u θ (psi φ)).re - torusR θ φ =
      (eval u θ (psi φ)).re - (torusR θ φ - 1) by ring]
    linarith
  · have h1 := norm_eval_le_of_Bd hr0 hC.dz θ (psi φ)
    rw [eval_sub', eval_z₀, phiOf_psi] at h1
    have h2 := (Complex.abs_re_le_norm _).trans h1
    simp only [Complex.sub_re, Complex.ofReal_re] at h2
    rw [Zof]
    linarith
  · have h1 := norm_eval_le_of_Bd hr0 hC.dut θ (psi φ)
    rw [eval_sub', dTh_u₀, eval_Rθ₀, phiOf_psi] at h1
    have h2 := (Complex.abs_re_le_norm _).trans h1
    simp only [Complex.sub_re, Complex.ofReal_re] at h2
    rw [(hasDerivAt_Rof_θ hu θ φ).deriv]
    linarith
  · have h1 := norm_eval_le_of_Bd hr0 hC.dzt θ (psi φ)
    rw [eval_sub', dTh_z₀, eval_zθ₀, phiOf_psi] at h1
    have h2 := (Complex.abs_re_le_norm _).trans h1
    simp only [Complex.sub_re, Complex.ofReal_re] at h2
    rw [(hasDerivAt_Zof_θ hz θ φ).deriv]
    linarith

end PlasmaLean.Design.KamNewton

namespace PlasmaLean.Design.RationalStellarator

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Design.KamTorusA
open PlasmaLean.Fields

/-- **All-time field-line confinement in the exact rational stellarator field (K4).** There is a
torus profile `ρ` (the radial graph, about the exact magnetic axis `R = 1, z = 0`, of the exact
KAM torus of rotational transform `ι = (75 + √5)/562` near torus A) with
`0.077 ≤ ρ ≤ 0.19`, such that every two-sided field line of `field (1/4)` starting on the axis or
strictly inside the torus stays inside it — in particular within distance `0.19` of the axis —
for all time, forward and backward. -/
theorem rationalStellarator_confined_forever :
    ∃ ρ : ℝ → ℝ → ℝ, TorusProfile ρ ∧ (∀ a b, 77 / 1000 ≤ ρ a b) ∧ (∀ a b, ρ a b ≤ 19 / 100) ∧
      ∀ {γ : ℝ → Space}, IsFieldLine (field (1 / 4)) γ →
        (rt (γ 0) = 0 ∨ rt (γ 0) < ρ (θs (γ 0)) (φs (γ 0))) →
        ∀ t, rt (γ t) ≤ 19 / 100 ∧ (rt (γ t) = 0 ∨ rt (γ t) < ρ (θs (γ t)) (φs (γ t))) := by
  obtain ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩ := torusA_exact
  exact rationalStellarator_confined_forever_of_exact (exactTorus hu hz hur hzr hR hZ hC)

/-- The exact torus behind `rationalStellarator_confined_forever`: a real `C²` torus of `field
(1/4)` with rotational transform exactly `ι = (75 + √5)/562`, `10⁻⁶`-close to torus A in `C¹`. -/
theorem rationalStellarator_exact_torus : ∃ Rk zk : ℝ → ℝ → ℝ, ExactTorus Rk zk := by
  obtain ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩ := torusA_exact
  exact ⟨_, _, exactTorus hu hz hur hzr hR hZ hC⟩

end PlasmaLean.Design.RationalStellarator
