/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Transport.RelativeEntropy

/-!
# Sanity checks for the corrected relative-entropy identity (N-2)

Degenerate and concrete cases of `PlasmaLean.Theory.Transport.RelativeEntropy`:

* `T = T*`: density, flux, Fisher, cross, boundary and diffusive rate all vanish.
* Constant reference: the cross term drops out and the identity becomes
  `(1 − c/T) F' = −κ c (T'/T)² + ∂ₓ[(1 − c/T) F]`.
* A concrete instance of note case 1 (`T = 1 + x − x²`, `T* = 1` on `[0, 1]`), so its hypotheses are
  satisfiable; the counterexample `old_identity_false` is the rejected fixture outside them.
* The scalar sign lemmas at concrete values, and the failure of the reaction sign for a source that
  increases with temperature (note case 3).
-/

public section

noncomputable section

namespace PlasmaLean.Sanity.RelativeEntropy

open Real Set MeasureTheory intervalIntegral PlasmaLean.Transport.RelativeEntropy

/-- The density vanishes at `T = T*`. -/
theorem density_self (n Ts : ℝ) (hTs : Ts ≠ 0) : relEntDensity n Ts Ts = 0 := by
  simp [relEntDensity, div_self hTs, phi_one]

/-- The relative-entropy flux vanishes at `T = T*`. -/
theorem flux_self (Ts F Fs : ℝ) (hTs : Ts ≠ 0) : relEntFlux Ts Ts F Fs = 0 := by
  simp [relEntFlux, div_self hTs]

/-- For `T = T*` on the interval every term of the integrated identity vanishes. -/
theorem setup_self {a b : ℝ} (S : RelEntSetup a b) (hT : ∀ x ∈ uIcc a b, S.T x = S.Ts x)
    (hdT : ∀ x ∈ uIcc a b, S.dT x = S.dTs x) :
    S.diffusion = 0 ∧ S.fisher = 0 ∧ S.cross = 0 ∧ S.boundary = 0 := by
  have hpos := S.Ts_pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold RelEntSetup.diffusion
    rw [integral_congr (g := fun _ => (0 : ℝ)) fun x hx => by
      simp [hT x hx, div_self (hpos x hx).ne']]
    simp
  · unfold RelEntSetup.fisher
    rw [integral_congr (g := fun _ => (0 : ℝ)) fun x hx => by simp [hT x hx, hdT x hx]]
    simp
  · unfold RelEntSetup.cross
    rw [integral_congr (g := fun _ => (0 : ℝ)) fun x hx => by
      simp [hT x hx, div_self (hpos x hx).ne']]
    simp
  · exact S.boundary_eq_zero_of_matched (hT a left_mem_uIcc) (hT b right_mem_uIcc)

/-- Constant reference `T* = c`: the identity has no cross term,
`(1 − c/T) F' = −κ c (T'/T)² + ∂ₓ[(1 − c/T) F]` (the flux derivative written out). -/
theorem const_ref_identity (κ c T dT dF : ℝ) (hT : T ≠ 0) (hc : c ≠ 0) :
    (1 - c / T) * dF =
      -(κ * c * (dT / T) ^ 2) + ((1 - c / T) * dF + (c * dT / T ^ 2) * (κ * dT)) := by
  have h := relEnt_core κ T c dT 0 dF 0 hT hc
  simp only [zero_div, sub_zero, mul_zero] at h
  linarith

/-- `φ(2) = 1 − log 2 > 0`. -/
theorem phi_two_pos : 0 < phi 2 := by
  unfold phi
  linarith [Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)]

/-- The scalar lemma of case 2 at `s = 2`. -/
example : 1 - 1 / (2 : ℝ) - Real.log 2 ≤ 0 := one_sub_inv_sub_log_nonpos (by norm_num)

/-- Note case 3 (rejected fixture): for a source increasing in temperature (`Q(T) = T`) the
reaction term `(1 − T*/T)(Q(T) − Q(T*))` is positive at `T = 2`, `T* = 1`. -/
theorem reaction_sign_fails_increasing :
    0 < (1 - (1 : ℝ) / 2) * ((2 : ℝ) - 1) := by norm_num

/-- A concrete instance of note case 1 on `[0, 1]`: `κ = 1`, `T = 1 + x − x²`, `T* = 1`. -/
def constRefSetup : RelEntSetup 0 1 where
  κ := fun _ => 1
  T := fun x => 1 + x - x ^ 2
  Ts := fun _ => 1
  dT := fun x => 1 - 2 * x
  dTs := fun _ => 0
  F := fun x => 1 - 2 * x
  Fs := fun _ => 0
  dF := fun _ => -2
  dFs := fun _ => 0
  T_pos := fun x hx => by
    rw [uIcc_of_le zero_le_one] at hx; nlinarith [hx.1, hx.2]
  Ts_pos := fun _ _ => one_pos
  hT := fun x _ => by
    have h := ((hasDerivAt_id x).const_add 1).sub (hasDerivAt_pow 2 x)
    convert h using 1
    · ext y; simp
    · simp
  hTs := fun x _ => hasDerivAt_const x 1
  hF := fun x _ => by
    have h := (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).const_mul 2)
    convert h using 1
    · ext y; simp
    · simp
  hFs := fun x _ => hasDerivAt_const x 0
  F_eq := fun x _ => by simp
  Fs_eq := fun x _ => by simp
  cont_κ := continuousOn_const
  cont_dT := (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn
  cont_dTs := continuousOn_const
  cont_dF := continuousOn_const
  cont_dFs := continuousOn_const

/-- Case 1 applies to `constRefSetup` (matched Dirichlet data, `Q = 0`, `∂ₜT = T''`): the entropy
rate equals `−𝓕` and is `≤ 0`. -/
theorem constRef_rate :
    ∫ x in (0 : ℝ)..1, 1 * (1 - constRefSetup.Ts x / constRefSetup.T x) * constRefSetup.dF x =
        -constRefSetup.fisher ∧
      ∫ x in (0 : ℝ)..1, 1 * (1 - constRefSetup.Ts x / constRefSetup.T x) *
        constRefSetup.dF x ≤ 0 :=
  constRefSetup.rate_le_neg_fisher_const_ref zero_le_one (n := fun _ => 1)
    (fun x _ => one_mul _) (fun _ _ => zero_le_one) (fun _ _ => rfl) (fun _ _ => rfl)
    (Or.inl (by norm_num [constRefSetup])) (Or.inl (by norm_num [constRefSetup]))

end PlasmaLean.Sanity.RelativeEntropy
