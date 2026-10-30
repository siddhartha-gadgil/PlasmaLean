/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The corrected relative-entropy identity for 1-D heat transport (N-2, gate E6)

Source: `notes/theory/relative-entropy-dissipation.md` (N-2), which corrects the identity in
`notes/bkm-regularity-and-perelman-burn-bounds.md` §3.1 (the old version omits the cross term and
the boundary terms, and writes `ΔQ` for `Q`). This module formalizes the 1-D version.

## Model

On an interval, a temperature `T > 0` evolves by `n ∂ₜT = ∂ₓF + Q` with flux `F = κ ∂ₓT`, where
`κ = nχ` is a coefficient **independent of `T`**. A fixed reference profile `T* > 0` has flux
`F* = κ ∂ₓT*`. With `φ(s) = s − 1 − log s` the relative-entropy density is `n T* φ(T/T*)`. Writing
`s = T/T*`, the corrected identity is

`(1 − T*/T) ∂ₓF = − κ T* (∂ₓ log s)² + log s · ∂ₓF* + ∂ₓ[(1 − T*/T) F − log s · F*]`,

so that `∂ₜ(n T* φ(s)) = −κT*(∂ₓ log s)² + log s · ∂ₓF* + (1 − T*/T) Q + ∂ₓ(flux)`.
Integrated over `[a, b]` this is `rate = −𝓕 + 𝓒 + 𝓡 + 𝓑` (Fisher, cross, reaction and boundary
terms).

The radial (flux-surface-averaged) model `V' n ∂ₜT = ∂ψ(V' n D ∂ψT) + V' Q` is the same identity
with `n ↦ V' n`, `κ ↦ V' n D` and `Q ↦ V' Q`, since all coefficients here are arbitrary
functions of `x`.

## Main results

* `hasDerivAt_relEntDensity_time`: `∂ₜ(n T* φ(T/T*)) = n (1 − T*/T) ∂ₜT`.
* `relEnt_flux_identity`: the pointwise spatial identity, with the Fisher term written as the
  square of `deriv (log (T/T*))` and the flux term as a `deriv`.
* `relEnt_pointwise_identity`: the combined space-time pointwise identity with the source.
* `RelEntSetup.integral_identity`, `RelEntSetup.rate_eq`: the integrated identity on `[a, b]`
  with explicit boundary terms.
* `RelEntSetup.rate_le_neg_fisher_const_ref` (note case 1) and
  `RelEntSetup.rate_le_neg_fisher_steady` (note case 2): the sign statements.
* `old_identity_false`: the counterexample `T* = 1 + x²`, `T = 1 + x` on `[0, 1]`, showing that
  the old identity without the cross term is false.

All solutions and derivatives are supplied (`HasDerivAt` hypotheses); no existence theorem is
claimed, and the time derivative is taken pointwise (differentiation under the integral sign is
not formalized here).
-/

public section

noncomputable section

namespace PlasmaLean.Transport.RelativeEntropy

open Real Set MeasureTheory intervalIntegral

/-- The relative-entropy generating function `φ(s) = s − 1 − log s`. -/
@[expose] def phi (s : ℝ) : ℝ := s - 1 - Real.log s

/-- The relative-entropy density `n T* φ(T/T*)`. -/
@[expose] def relEntDensity (n Ts T : ℝ) : ℝ := n * Ts * phi (T / Ts)

/-- The relative-entropy flux `(1 − T*/T) F − log(T/T*) F*`, whose derivative is the
divergence term of the identity and whose endpoint values are the boundary terms. -/
@[expose] def relEntFlux (T Ts F Fs : ℝ) : ℝ := (1 - Ts / T) * F - Real.log (T / Ts) * Fs

/-! ## Scalar lemmas -/

/-- `φ ≥ 0` on `(0, ∞)`. -/
theorem phi_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ phi s := by
  unfold phi; linarith [Real.log_le_sub_one_of_pos hs]

/-- `φ(1) = 0`. -/
theorem phi_one : phi 1 = 0 := by simp [phi]

/-- The relative-entropy density is nonnegative for `n ≥ 0`, `T, T* > 0`. -/
theorem relEntDensity_nonneg {n Ts T : ℝ} (hn : 0 ≤ n) (hTs : 0 < Ts) (hT : 0 < T) :
    0 ≤ relEntDensity n Ts T :=
  mul_nonneg (mul_nonneg hn hTs.le) (phi_nonneg (div_pos hT hTs))

/-- The scalar lemma of note case 2: `1 − 1/s − log s ≤ 0` for `s > 0`. -/
theorem one_sub_inv_sub_log_nonpos {s : ℝ} (hs : 0 < s) : 1 - 1 / s - Real.log s ≤ 0 := by
  have := Real.one_sub_inv_le_log_of_pos hs
  rw [one_div]; linarith

/-- The monotone-loss sign lemma of note case 2: if `Q` is non-increasing in temperature then
`(1 − T*/T)(Q(T) − Q(T*)) ≤ 0`. -/
theorem reaction_monotone_nonpos {T Ts QT QTs : ℝ} (hT : 0 < T)
    (hmono : Ts ≤ T → QT ≤ QTs) (hmono' : T ≤ Ts → QTs ≤ QT) :
    (1 - Ts / T) * (QT - QTs) ≤ 0 := by
  rcases le_total Ts T with h | h
  · have h1 : 0 ≤ 1 - Ts / T := by
      rw [sub_nonneg, div_le_one hT]; exact h
    exact mul_nonpos_of_nonneg_of_nonpos h1 (by linarith [hmono h])
  · have h1 : 1 - Ts / T ≤ 0 := by
      rw [sub_nonpos, one_le_div hT]; exact h
    exact mul_nonpos_of_nonpos_of_nonneg h1 (by linarith [hmono' h])

/-- The pointwise reaction sign of note case 2: for a steady reference (`∂ₓF* = −Q(T*)`), with
`Q(T*) ≥ 0` and `Q` non-increasing in temperature, cross plus reaction is `≤ 0`. -/
theorem cross_add_reaction_nonpos_steady {T Ts dFs QT QTs : ℝ} (hT : 0 < T) (hTs : 0 < Ts)
    (hsteady : dFs + QTs = 0) (hQ : 0 ≤ QTs)
    (hmono : Ts ≤ T → QT ≤ QTs) (hmono' : T ≤ Ts → QTs ≤ QT) :
    Real.log (T / Ts) * dFs + (1 - Ts / T) * QT ≤ 0 := by
  have hs : 0 < T / Ts := div_pos hT hTs
  have h1 := one_sub_inv_sub_log_nonpos hs
  have h2 := reaction_monotone_nonpos (Ts := Ts) hT hmono hmono'
  have hinv : 1 / (T / Ts) = Ts / T := by rw [one_div, inv_div]
  rw [hinv] at h1
  have hdFs : dFs = -QTs := by linarith
  have : Real.log (T / Ts) * dFs + (1 - Ts / T) * QT =
      (1 - Ts / T - Real.log (T / Ts)) * QTs + (1 - Ts / T) * (QT - QTs) := by
    rw [hdFs]; ring
  rw [this]
  nlinarith [mul_nonpos_of_nonpos_of_nonneg h1 hQ]

/-! ## Pointwise identities -/

/-- Time derivative of the relative-entropy density at a fixed point:
`∂ₜ(n T* φ(T/T*)) = n (1 − T*/T) ∂ₜT`. -/
theorem hasDerivAt_relEntDensity_time {n Ts : ℝ} {T : ℝ → ℝ} {Tt t : ℝ} (hTs : 0 < Ts)
    (hT : 0 < T t) (h : HasDerivAt T Tt t) :
    HasDerivAt (fun τ => relEntDensity n Ts (T τ)) (n * (1 - Ts / T t) * Tt) t := by
  have hs : T t / Ts ≠ 0 := (div_pos hT hTs).ne'
  have h1 := ((h.div_const Ts).sub_const 1).sub ((h.div_const Ts).log hs)
  have h2 := h1.const_mul (n * Ts)
  unfold relEntDensity phi
  convert h2 using 1
  field_simp

/-- Derivative of the log-ratio: `∂ₓ log(T/T*) = T'/T − T*'/T*`. -/
theorem hasDerivAt_log_ratio {T Ts : ℝ → ℝ} {dT dTs x : ℝ} (hT : 0 < T x) (hTs : 0 < Ts x)
    (h1 : HasDerivAt T dT x) (h2 : HasDerivAt Ts dTs x) :
    HasDerivAt (fun y => Real.log (T y / Ts y)) (dT / T x - dTs / Ts x) x := by
  have h12 : HasDerivAt (fun y => T y / Ts y) ((dT * Ts x - T x * dTs) / Ts x ^ 2) x :=
    h1.div h2 hTs.ne'
  have h := h12.log (div_pos hT hTs).ne'
  convert h using 1
  field_simp

/-- Derivative of the relative-entropy flux `(1 − T*/T) F − log(T/T*) F*`. -/
theorem hasDerivAt_relEntFlux {T Ts F Fs : ℝ → ℝ} {dT dTs dF dFs x : ℝ} (hT : 0 < T x)
    (hTs : 0 < Ts x) (h1 : HasDerivAt T dT x) (h2 : HasDerivAt Ts dTs x)
    (h3 : HasDerivAt F dF x) (h4 : HasDerivAt Fs dFs x) :
    HasDerivAt (fun y => relEntFlux (T y) (Ts y) (F y) (Fs y))
      ((1 - Ts x / T x) * dF + (Ts x * dT / T x ^ 2 - dTs / T x) * F x
        - (dT / T x - dTs / Ts x) * Fs x - Real.log (T x / Ts x) * dFs) x := by
  have h21 : HasDerivAt (fun y => Ts y / T y) ((dTs * T x - Ts x * dT) / T x ^ 2) x :=
    h2.div h1 hT.ne'
  have hq : HasDerivAt (fun y => (1 - Ts y / T y) * F y)
      (-((dTs * T x - Ts x * dT) / T x ^ 2) * F x + (1 - Ts x / T x) * dF) x :=
    (h21.const_sub 1).mul h3
  have hl := (hasDerivAt_log_ratio hT hTs h1 h2).mul h4
  unfold relEntFlux
  convert hq.sub hl using 1
  field_simp
  ring

/-- The algebraic core of the identity: for `F = κT'`, `F* = κT*'`,
`(1 − T*/T) F' = −κT*(T'/T − T*'/T*)² + log(T/T*) F*' + (flux)'`. -/
theorem relEnt_core (κ T Ts dT dTs dF dFs : ℝ) (hT : T ≠ 0) (hTs : Ts ≠ 0) :
    (1 - Ts / T) * dF = -(κ * Ts * (dT / T - dTs / Ts) ^ 2) + Real.log (T / Ts) * dFs
      + ((1 - Ts / T) * dF + (Ts * dT / T ^ 2 - dTs / T) * (κ * dT)
        - (dT / T - dTs / Ts) * (κ * dTs) - Real.log (T / Ts) * dFs) := by
  field_simp
  ring

/-- **The corrected pointwise relative-entropy identity (1-D, spatial part).** For `T, T* > 0`
differentiable at `x`, with fluxes `F = κT'`, `F* = κT*'` differentiable at `x`:
`(1 − T*/T) F' = −κ T* (∂ₓ log(T/T*))² + log(T/T*) F*' + ∂ₓ[(1 − T*/T) F − log(T/T*) F*]`. -/
theorem relEnt_flux_identity {κ : ℝ} {T Ts F Fs : ℝ → ℝ} {dT dTs dF dFs x : ℝ} (hT : 0 < T x)
    (hTs : 0 < Ts x) (h1 : HasDerivAt T dT x) (h2 : HasDerivAt Ts dTs x)
    (h3 : HasDerivAt F dF x) (h4 : HasDerivAt Fs dFs x) (hF : F x = κ * dT)
    (hFs : Fs x = κ * dTs) :
    (1 - Ts x / T x) * dF =
      -(κ * Ts x * (deriv (fun y => Real.log (T y / Ts y)) x) ^ 2)
        + Real.log (T x / Ts x) * dFs
        + deriv (fun y => relEntFlux (T y) (Ts y) (F y) (Fs y)) x := by
  rw [(hasDerivAt_log_ratio hT hTs h1 h2).deriv, (hasDerivAt_relEntFlux hT hTs h1 h2 h3 h4).deriv,
    hF, hFs]
  exact relEnt_core κ (T x) (Ts x) dT dTs dF dFs hT.ne' hTs.ne'

/-- The equivalent un-integrated form of the note:
`(1 − T*/T) F' = −κT* T'²/T² + κ T*' T'/T + ∂ₓ[(1 − T*/T) F]`. -/
theorem relEnt_flux_identity_unintegrated {κ : ℝ} {T Ts F : ℝ → ℝ} {dT dTs dF x : ℝ}
    (hT : 0 < T x) (h1 : HasDerivAt T dT x) (h2 : HasDerivAt Ts dTs x)
    (h3 : HasDerivAt F dF x) (hF : F x = κ * dT) :
    (1 - Ts x / T x) * dF =
      -(κ * Ts x * dT ^ 2 / T x ^ 2) + κ * dTs * dT / T x
        + deriv (fun y => (1 - Ts y / T y) * F y) x := by
  have h21 : HasDerivAt (fun y => Ts y / T y) ((dTs * T x - Ts x * dT) / T x ^ 2) x :=
    h2.div h1 hT.ne'
  have hq : HasDerivAt (fun y => (1 - Ts y / T y) * F y)
      (-((dTs * T x - Ts x * dT) / T x ^ 2) * F x + (1 - Ts x / T x) * dF) x :=
    (h21.const_sub 1).mul h3
  rw [hq.deriv, hF]
  field_simp
  ring

/-- **The corrected pointwise relative-entropy identity (1-D, space-time).** Let `T(t, x) > 0`
solve `n ∂ₜT = ∂ₓF + Q` at `(t, x)` with `F = κ ∂ₓT`, and let `T*(x) > 0` have flux `F* = κ ∂ₓT*`.
Then `∂ₜ(n T* φ(T/T*))` equals
`−κ T* (∂ₓ log(T/T*))² + log(T/T*) ∂ₓF* + (1 − T*/T) Q + ∂ₓ[(1 − T*/T) F − log(T/T*) F*]`:
Fisher, cross, reaction (with `Q`, not `ΔQ`) and divergence terms. -/
theorem relEnt_pointwise_identity {n κ Q : ℝ} {T : ℝ → ℝ → ℝ} {Ts F Fs : ℝ → ℝ}
    {t x Tt dT dTs dF dFs : ℝ} (hT : 0 < T t x) (hTs : 0 < Ts x)
    (ht : HasDerivAt (fun τ => T τ x) Tt t) (h1 : HasDerivAt (T t) dT x)
    (h2 : HasDerivAt Ts dTs x) (h3 : HasDerivAt F dF x) (h4 : HasDerivAt Fs dFs x)
    (hF : F x = κ * dT) (hFs : Fs x = κ * dTs) (hpde : n * Tt = dF + Q) :
    HasDerivAt (fun τ => relEntDensity n (Ts x) (T τ x))
      (-(κ * Ts x * (deriv (fun y => Real.log (T t y / Ts y)) x) ^ 2)
        + Real.log (T t x / Ts x) * dFs + (1 - Ts x / T t x) * Q
        + deriv (fun y => relEntFlux (T t y) (Ts y) (F y) (Fs y)) x) t := by
  have h := hasDerivAt_relEntDensity_time (n := n) (T := fun τ => T τ x) hTs hT ht
  have hid := relEnt_flux_identity (T := T t) hT hTs h1 h2 h3 h4 hF hFs
  convert h using 1
  rw [mul_assoc, mul_comm n, mul_assoc, hpde]
  linear_combination -hid

/-! ## The integrated identity on `[a, b]` -/

/-- Supplied 1-D data on `[a, b]` (`uIcc a b`) at a fixed time: coefficient `κ`, temperature `T`
and reference `T*` (both positive), their derivatives, fluxes `F = κT'`, `F* = κT*'` and the flux
derivatives. The derivative functions are assumed continuous so that every term is integrable. -/
structure RelEntSetup (a b : ℝ) where
  /-- The diffusion coefficient `κ = nχ` (independent of `T`). -/
  κ : ℝ → ℝ
  /-- The temperature at the fixed time. -/
  T : ℝ → ℝ
  /-- The reference profile `T*`. -/
  Ts : ℝ → ℝ
  /-- `∂ₓT`. -/
  dT : ℝ → ℝ
  /-- `∂ₓT*`. -/
  dTs : ℝ → ℝ
  /-- The heat flux `F = κ ∂ₓT`. -/
  F : ℝ → ℝ
  /-- The reference flux `F* = κ ∂ₓT*`. -/
  Fs : ℝ → ℝ
  /-- `∂ₓF`. -/
  dF : ℝ → ℝ
  /-- `∂ₓF*`. -/
  dFs : ℝ → ℝ
  /-- `T > 0` on the interval. -/
  T_pos : ∀ x ∈ uIcc a b, 0 < T x
  /-- `T* > 0` on the interval. -/
  Ts_pos : ∀ x ∈ uIcc a b, 0 < Ts x
  /-- `dT` is the derivative of `T`. -/
  hT : ∀ x ∈ uIcc a b, HasDerivAt T (dT x) x
  /-- `dTs` is the derivative of `T*`. -/
  hTs : ∀ x ∈ uIcc a b, HasDerivAt Ts (dTs x) x
  /-- `dF` is the derivative of `F`. -/
  hF : ∀ x ∈ uIcc a b, HasDerivAt F (dF x) x
  /-- `dFs` is the derivative of `F*`. -/
  hFs : ∀ x ∈ uIcc a b, HasDerivAt Fs (dFs x) x
  /-- The constitutive law `F = κ T'`. -/
  F_eq : ∀ x ∈ uIcc a b, F x = κ x * dT x
  /-- The constitutive law `F* = κ T*'`. -/
  Fs_eq : ∀ x ∈ uIcc a b, Fs x = κ x * dTs x
  /-- Continuity of `κ`. -/
  cont_κ : ContinuousOn κ (uIcc a b)
  /-- Continuity of `T'`. -/
  cont_dT : ContinuousOn dT (uIcc a b)
  /-- Continuity of `T*'`. -/
  cont_dTs : ContinuousOn dTs (uIcc a b)
  /-- Continuity of `F'`. -/
  cont_dF : ContinuousOn dF (uIcc a b)
  /-- Continuity of `F*'`. -/
  cont_dFs : ContinuousOn dFs (uIcc a b)

namespace RelEntSetup

variable {a b : ℝ} (S : RelEntSetup a b)

/-- The Fisher-type information `𝓕 = ∫ κ T* (∂ₓ log(T/T*))²`. -/
@[expose] def fisher : ℝ := ∫ x in a..b, S.κ x * S.Ts x * (S.dT x / S.T x - S.dTs x / S.Ts x) ^ 2

/-- The cross term `𝓒 = ∫ log(T/T*) ∂ₓF*` (no sign in general). -/
@[expose] def cross : ℝ := ∫ x in a..b, Real.log (S.T x / S.Ts x) * S.dFs x

/-- The boundary term `𝓑 = [(1 − T*/T) F − log(T/T*) F*]` evaluated between `a` and `b`. -/
@[expose] def boundary : ℝ :=
  relEntFlux (S.T b) (S.Ts b) (S.F b) (S.Fs b) - relEntFlux (S.T a) (S.Ts a) (S.F a) (S.Fs a)

/-- The diffusive part of the entropy rate, `∫ (1 − T*/T) ∂ₓF`. -/
@[expose] def diffusion : ℝ := ∫ x in a..b, (1 - S.Ts x / S.T x) * S.dF x

/-- `T` is continuous on the interval. -/
theorem contT : ContinuousOn S.T (uIcc a b) :=
  fun x hx => (S.hT x hx).continuousAt.continuousWithinAt

/-- `T*` is continuous on the interval. -/
theorem contTs : ContinuousOn S.Ts (uIcc a b) :=
  fun x hx => (S.hTs x hx).continuousAt.continuousWithinAt

/-- `F` is continuous on the interval. -/
theorem contF : ContinuousOn S.F (uIcc a b) :=
  fun x hx => (S.hF x hx).continuousAt.continuousWithinAt

/-- `F*` is continuous on the interval. -/
theorem contFs : ContinuousOn S.Fs (uIcc a b) :=
  fun x hx => (S.hFs x hx).continuousAt.continuousWithinAt

/-- `T*/T` is continuous on the interval. -/
theorem cont_ratio : ContinuousOn (fun x => S.Ts x / S.T x) (uIcc a b) :=
  S.contTs.div S.contT fun x hx => (S.T_pos x hx).ne'

/-- `log(T/T*)` is continuous on the interval. -/
theorem cont_log : ContinuousOn (fun x => Real.log (S.T x / S.Ts x)) (uIcc a b) :=
  (S.contT.div S.contTs fun x hx => (S.Ts_pos x hx).ne').log
    fun x hx => (div_pos (S.T_pos x hx) (S.Ts_pos x hx)).ne'

/-- The Fisher integrand is continuous on the interval. -/
theorem cont_fisher :
    ContinuousOn (fun x => S.κ x * S.Ts x * (S.dT x / S.T x - S.dTs x / S.Ts x) ^ 2)
      (uIcc a b) :=
  (S.cont_κ.mul S.contTs).mul (((S.cont_dT.div S.contT fun x hx => (S.T_pos x hx).ne').sub
    (S.cont_dTs.div S.contTs fun x hx => (S.Ts_pos x hx).ne')).pow 2)

/-- The cross integrand is continuous on the interval. -/
theorem cont_cross : ContinuousOn (fun x => Real.log (S.T x / S.Ts x) * S.dFs x) (uIcc a b) :=
  S.cont_log.mul S.cont_dFs

/-- The diffusion integrand is continuous on the interval. -/
theorem cont_diffusion : ContinuousOn (fun x => (1 - S.Ts x / S.T x) * S.dF x) (uIcc a b) :=
  (continuousOn_const.sub S.cont_ratio).mul S.cont_dF

/-- The derivative of the relative-entropy flux, as a function on the interval. -/
@[expose] def fluxDeriv (x : ℝ) : ℝ :=
  (1 - S.Ts x / S.T x) * S.dF x + (S.Ts x * S.dT x / S.T x ^ 2 - S.dTs x / S.T x) * S.F x
    - (S.dT x / S.T x - S.dTs x / S.Ts x) * S.Fs x - Real.log (S.T x / S.Ts x) * S.dFs x

/-- Pointwise form of the identity on the interval. -/
theorem diffusion_integrand_eq {x : ℝ} (hx : x ∈ uIcc a b) :
    (1 - S.Ts x / S.T x) * S.dF x =
      -(S.κ x * S.Ts x * (S.dT x / S.T x - S.dTs x / S.Ts x) ^ 2)
        + Real.log (S.T x / S.Ts x) * S.dFs x + S.fluxDeriv x := by
  unfold fluxDeriv
  rw [S.F_eq x hx, S.Fs_eq x hx]
  exact relEnt_core _ _ _ _ _ _ _ (S.T_pos x hx).ne' (S.Ts_pos x hx).ne'

/-- The flux derivative is continuous on the interval. -/
theorem cont_fluxDeriv : ContinuousOn S.fluxDeriv (uIcc a b) := by
  have h : ContinuousOn (fun x => (1 - S.Ts x / S.T x) * S.dF x
      + S.κ x * S.Ts x * (S.dT x / S.T x - S.dTs x / S.Ts x) ^ 2
      - Real.log (S.T x / S.Ts x) * S.dFs x) (uIcc a b) :=
    (S.cont_diffusion.add S.cont_fisher).sub S.cont_cross
  refine h.congr fun x hx => ?_
  simp only
  rw [S.diffusion_integrand_eq hx]
  ring

/-- **Integrated corrected identity (diffusive part).** On `[a, b]`,
`∫ (1 − T*/T) F' = −𝓕 + 𝓒 + 𝓑`. -/
theorem integral_identity : S.diffusion = -S.fisher + S.cross + S.boundary := by
  have hB : ∫ x in a..b, S.fluxDeriv x = S.boundary :=
    integral_eq_sub_of_hasDerivAt
      (fun x hx => hasDerivAt_relEntFlux (S.T_pos x hx) (S.Ts_pos x hx) (S.hT x hx) (S.hTs x hx)
        (S.hF x hx) (S.hFs x hx))
      (S.cont_fluxDeriv.intervalIntegrable (μ := volume))
  have hfi := S.cont_fisher.intervalIntegrable (μ := volume)
  have hci := S.cont_cross.intervalIntegrable (μ := volume)
  have hdi := S.cont_fluxDeriv.intervalIntegrable (μ := volume)
  unfold diffusion fisher cross
  have hfi' : IntervalIntegrable
      (fun x => -(S.κ x * S.Ts x * (S.dT x / S.T x - S.dTs x / S.Ts x) ^ 2)) volume a b := hfi.neg
  have hfc : IntervalIntegrable
      (fun x => -(S.κ x * S.Ts x * (S.dT x / S.T x - S.dTs x / S.Ts x) ^ 2)
        + Real.log (S.T x / S.Ts x) * S.dFs x) volume a b := hfi'.add hci
  rw [integral_congr fun x hx => S.diffusion_integrand_eq hx, integral_add hfc hdi,
    integral_add hfi' hci, intervalIntegral.integral_neg, hB]

/-- The Fisher information is nonnegative when `κ ≥ 0` and `a ≤ b`. -/
theorem fisher_nonneg (hab : a ≤ b) (hκ : ∀ x ∈ uIcc a b, 0 ≤ S.κ x) : 0 ≤ S.fisher := by
  unfold fisher
  refine integral_nonneg hab fun x hx => ?_
  have hx' : x ∈ uIcc a b := by rw [uIcc_of_le hab]; exact hx
  exact mul_nonneg (mul_nonneg (hκ x hx') (S.Ts_pos x hx').le) (sq_nonneg _)

/-- The boundary term vanishes under matched Dirichlet data `T = T*` at both endpoints. -/
theorem boundary_eq_zero_of_matched (ha : S.T a = S.Ts a) (hb : S.T b = S.Ts b) :
    S.boundary = 0 := by
  have ha' : 0 < S.T a := S.T_pos a left_mem_uIcc
  have hb' : 0 < S.T b := S.T_pos b right_mem_uIcc
  unfold boundary relEntFlux
  rw [ha, hb] at *
  simp [div_self ha'.ne', div_self hb'.ne']

/-! ### The entropy rate with the evolution equation -/

/-- **Integrated corrected identity (full rate).** If `n ∂ₜT = F' + Q` on `[a, b]` (with `Tt`
the time derivative at the fixed time and `n`, `Q` continuous), then the pointwise entropy rate
`∫ n (1 − T*/T) ∂ₜT` equals `−𝓕 + 𝓒 + 𝓡 + 𝓑`, with reaction `𝓡 = ∫ (1 − T*/T) Q`. -/
theorem rate_eq {n Tt Q : ℝ → ℝ} (hpde : ∀ x ∈ uIcc a b, n x * Tt x = S.dF x + Q x)
    (hQ : ContinuousOn Q (uIcc a b)) :
    ∫ x in a..b, n x * (1 - S.Ts x / S.T x) * Tt x =
      -S.fisher + S.cross + (∫ x in a..b, (1 - S.Ts x / S.T x) * Q x) + S.boundary := by
  have hR : ContinuousOn (fun x => (1 - S.Ts x / S.T x) * Q x) (uIcc a b) :=
    (continuousOn_const.sub S.cont_ratio).mul hQ
  have h : ∫ x in a..b, n x * (1 - S.Ts x / S.T x) * Tt x =
      ∫ x in a..b, ((1 - S.Ts x / S.T x) * S.dF x + (1 - S.Ts x / S.T x) * Q x) := by
    refine integral_congr fun x hx => ?_
    rw [mul_comm (n x), mul_assoc, hpde x hx]
    ring
  rw [h, integral_add S.cont_diffusion.intervalIntegrable hR.intervalIntegrable]
  have := S.integral_identity
  unfold diffusion at this
  rw [this]
  ring

/-- **Note case 1 (constant reference).** If `T*' = 0` and `F*' = 0` on `[a, b]`, `Q = 0`, `κ ≥ 0`,
and at each endpoint either `T = T*` (matched Dirichlet) or `F = 0` (no flux), then the entropy
rate equals `−𝓕 ≤ 0`. -/
theorem rate_le_neg_fisher_const_ref (hab : a ≤ b) {n Tt : ℝ → ℝ}
    (hpde : ∀ x ∈ uIcc a b, n x * Tt x = S.dF x) (hκ : ∀ x ∈ uIcc a b, 0 ≤ S.κ x)
    (hdTs : ∀ x ∈ uIcc a b, S.dTs x = 0) (hdFs : ∀ x ∈ uIcc a b, S.dFs x = 0)
    (ha : S.T a = S.Ts a ∨ S.F a = 0) (hb : S.T b = S.Ts b ∨ S.F b = 0) :
    ∫ x in a..b, n x * (1 - S.Ts x / S.T x) * Tt x = -S.fisher ∧
      ∫ x in a..b, n x * (1 - S.Ts x / S.T x) * Tt x ≤ 0 := by
  have hr := S.rate_eq (Q := fun _ => 0) (by simpa using hpde) continuousOn_const
  have hc : S.cross = 0 := by
    unfold cross
    rw [integral_congr (g := fun _ => (0 : ℝ)) fun x hx => by simp [hdFs x hx]]
    simp
  have hFs : ∀ x ∈ uIcc a b, S.Fs x = 0 := fun x hx => by rw [S.Fs_eq x hx, hdTs x hx, mul_zero]
  have hend : ∀ y ∈ uIcc a b, (S.T y = S.Ts y ∨ S.F y = 0) →
      relEntFlux (S.T y) (S.Ts y) (S.F y) (S.Fs y) = 0 := by
    intro y hy h
    unfold relEntFlux
    rw [hFs y hy, mul_zero, sub_zero]
    rcases h with h | h
    · rw [h, div_self (S.Ts_pos y hy).ne', sub_self, zero_mul]
    · rw [h, mul_zero]
  have hB : S.boundary = 0 := by
    unfold boundary; rw [hend a left_mem_uIcc ha, hend b right_mem_uIcc hb, sub_zero]
  have he : ∫ x in a..b, n x * (1 - S.Ts x / S.T x) * Tt x = -S.fisher := by
    rw [hr, hc, hB]; simp
  exact ⟨he, by rw [he]; linarith [S.fisher_nonneg hab hκ]⟩

/-- **Note case 2 (steady, Dirichlet-matched reference).** Let `Q(x, T)` be the source. If the
reference is steady (`F*' + Q(x, T*) = 0`), `Q(x, T*) ≥ 0`, `T ↦ Q(x, T)` is non-increasing,
`κ ≥ 0`, and `T = T*` at both endpoints, then the entropy rate is `≤ −𝓕 ≤ 0`. -/
theorem rate_le_neg_fisher_steady (hab : a ≤ b) {n Tt : ℝ → ℝ} {Q : ℝ → ℝ → ℝ}
    (hpde : ∀ x ∈ uIcc a b, n x * Tt x = S.dF x + Q x (S.T x))
    (hQT : ContinuousOn (fun x => Q x (S.T x)) (uIcc a b))
    (hκ : ∀ x ∈ uIcc a b, 0 ≤ S.κ x)
    (hsteady : ∀ x ∈ uIcc a b, S.dFs x + Q x (S.Ts x) = 0)
    (hQs : ∀ x ∈ uIcc a b, 0 ≤ Q x (S.Ts x))
    (hmono : ∀ x ∈ uIcc a b, ∀ u v, 0 < u → u ≤ v → Q x v ≤ Q x u)
    (ha : S.T a = S.Ts a) (hb : S.T b = S.Ts b) :
    ∫ x in a..b, n x * (1 - S.Ts x / S.T x) * Tt x ≤ -S.fisher ∧ -S.fisher ≤ 0 := by
  have hr := S.rate_eq (Q := fun x => Q x (S.T x)) hpde hQT
  have hR : ContinuousOn (fun x => (1 - S.Ts x / S.T x) * Q x (S.T x)) (uIcc a b) :=
    (continuousOn_const.sub S.cont_ratio).mul hQT
  have hsum : S.cross + ∫ x in a..b, (1 - S.Ts x / S.T x) * Q x (S.T x) ≤ 0 := by
    unfold cross
    rw [← integral_add S.cont_cross.intervalIntegrable hR.intervalIntegrable]
    have hle := integral_mono_on (μ := volume) hab (S.cont_cross.add hR).intervalIntegrable
      (intervalIntegrable_const (c := (0 : ℝ))) fun x hx => by
        have hx' : x ∈ uIcc a b := by rw [uIcc_of_le hab]; exact hx
        have hT := S.T_pos x hx'
        have hTs := S.Ts_pos x hx'
        exact cross_add_reaction_nonpos_steady hT hTs (hsteady x hx') (hQs x hx')
          (fun h => hmono x hx' _ _ hTs h) (fun h => hmono x hx' _ _ hT h)
    simpa using hle
  have hB := S.boundary_eq_zero_of_matched ha hb
  refine ⟨?_, by linarith [S.fisher_nonneg hab hκ]⟩
  rw [hr, hB]
  linarith

end RelEntSetup

/-! ## The counterexample to the old identity -/

/-- The counterexample data of N-2 on `[0, 1]`: `κ = 1`, `T = 1 + x`, `T* = 1 + x²`. -/
@[expose] def cexSetup : RelEntSetup 0 1 where
  κ := fun _ => 1
  T := fun x => 1 + x
  Ts := fun x => 1 + x ^ 2
  dT := fun _ => 1
  dTs := fun x => 2 * x
  F := fun _ => 1
  Fs := fun x => 2 * x
  dF := fun _ => 0
  dFs := fun _ => 2
  T_pos := fun x hx => by
    rw [uIcc_of_le zero_le_one] at hx; linarith [hx.1]
  Ts_pos := fun x _ => by positivity
  hT := fun x _ => by simpa using (hasDerivAt_id x).const_add 1
  hTs := fun x _ => by
    simpa using ((hasDerivAt_pow 2 x).const_add 1)
  hF := fun x _ => hasDerivAt_const x 1
  hFs := fun x _ => by simpa using (hasDerivAt_id x).const_mul 2
  F_eq := fun x _ => by simp
  Fs_eq := fun x _ => by simp
  cont_κ := continuousOn_const
  cont_dT := continuousOn_const
  cont_dTs := (continuous_const.mul continuous_id).continuousOn
  cont_dF := continuousOn_const
  cont_dFs := continuousOn_const

/-- In the counterexample the diffusive entropy rate vanishes, since `T'' = 0`. -/
theorem cexSetup_diffusion : cexSetup.diffusion = 0 := by
  simp [RelEntSetup.diffusion, cexSetup]

/-- In the counterexample `T = T*` at both endpoints, so the boundary term vanishes. -/
theorem cexSetup_boundary : cexSetup.boundary = 0 :=
  cexSetup.boundary_eq_zero_of_matched (by norm_num [cexSetup]) (by norm_num [cexSetup])

/-- In the counterexample the Fisher information is strictly positive. -/
theorem cexSetup_fisher_pos : 0 < cexSetup.fisher := by
  set f : ℝ → ℝ := fun x => 1 * (1 + x ^ 2) * (1 / (1 + x) - 2 * x / (1 + x ^ 2)) ^ 2 with hf
  have hfis : cexSetup.fisher = ∫ x in (0 : ℝ)..1, f x := rfl
  have hcont : ContinuousOn f (uIcc 0 1) := cexSetup.cont_fisher
  have hsub1 : uIcc (0 : ℝ) (1 / 4) ⊆ uIcc 0 1 := uIcc_subset_uIcc left_mem_uIcc (by
    rw [uIcc_of_le zero_le_one]; constructor <;> norm_num)
  have hsub2 : uIcc (1 / 4 : ℝ) 1 ⊆ uIcc 0 1 := uIcc_subset_uIcc (by
    rw [uIcc_of_le zero_le_one]; constructor <;> norm_num) right_mem_uIcc
  have hi1 : IntervalIntegrable f volume 0 (1 / 4) := (hcont.mono hsub1).intervalIntegrable
  have hi2 : IntervalIntegrable f volume (1 / 4) 1 := (hcont.mono hsub2).intervalIntegrable
  have hpos : 0 < ∫ x in (0 : ℝ)..(1 / 4), f x := by
    refine intervalIntegral_pos_of_pos_on hi1 (fun x hx => ?_) (by norm_num)
    obtain ⟨h0, h1⟩ := hx
    have hlt : 2 * x / (1 + x ^ 2) < 1 / (1 + x) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have : 0 < 1 / (1 + x) - 2 * x / (1 + x ^ 2) := sub_pos.2 hlt
    simp only [hf]
    positivity
  have hnn : 0 ≤ ∫ x in (1 / 4 : ℝ)..1, f x :=
    integral_nonneg (by norm_num) fun x _ => by simp only [hf]; positivity
  rw [hfis, ← integral_add_adjacent_intervals hi1 hi2]
  linarith

/-- In the counterexample the cross term exactly cancels the Fisher term: `𝓒 = 𝓕 > 0`. -/
theorem cexSetup_cross_eq_fisher : cexSetup.cross = cexSetup.fisher := by
  have h := cexSetup.integral_identity
  rw [cexSetup_diffusion, cexSetup_boundary] at h
  linarith

/-- **The old identity is false.** The identity of the BKM note §3.1 (rate `= −𝓕`, i.e. without
the cross and boundary terms) fails for the smooth data `T* = 1 + x²`, `T = 1 + x` on `[0, 1]`
with `κ = 1`: the true diffusive rate is `0`, while `−𝓕 < 0`. -/
theorem old_identity_false : ¬ ∀ S : RelEntSetup 0 1, S.diffusion = -S.fisher := by
  intro h
  have := h cexSetup
  rw [cexSetup_diffusion] at this
  linarith [cexSetup_fisher_pos]

/-- The old identity also fails for the full rate: with `n = 1`, `Q = 0` and `∂ₜT = T''` the
counterexample has rate `∫ (1 − T*/T) ∂ₜT = 0 ≠ −𝓕`. -/
theorem old_rate_identity_false :
    (∫ x in (0 : ℝ)..1, 1 * (1 - cexSetup.Ts x / cexSetup.T x) * cexSetup.dF x) = 0 ∧
      -cexSetup.fisher < 0 := by
  refine ⟨?_, by linarith [cexSetup_fisher_pos]⟩
  have hr := cexSetup.rate_eq (n := fun _ => 1) (Tt := cexSetup.dF) (Q := fun _ => 0)
    (fun x _ => by simp) continuousOn_const
  rw [hr, cexSetup_cross_eq_fisher, cexSetup_boundary]
  simp

end PlasmaLean.Transport.RelativeEntropy
