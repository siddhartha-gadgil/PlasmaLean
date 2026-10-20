/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Transport.PowerBalance
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Empirical energy-confinement scaling laws and the 0-D burn window

Track T4 of `notes/implementation-plan.md`: replace the ad-hoc, state-dependent `τ_E`
hypotheses of model rung M1 (`Design.BurnWindow`) by a **supplied empirical scaling law**.

## Scaling laws (supplied empirical fits, not derived)

* **IPB98(y,2)** (ITER Physics Basis, Nucl. Fusion **39** (1999) 2175, ch. 2, eq. (20)):
  `τ_E = 0.0562 H I_p^0.93 B^0.15 P^−0.69 n₁₉^0.41 M^0.19 R^1.97 ε^0.58 κ^0.78`
  (s; `I_p` in MA, `B` in T, `P` in MW, `n₁₉` in 10¹⁹ m⁻³, `M` in amu, `R` in m;
  `κ = κ_a` is the area elongation). `TokamakParams.ipb98`.
* **ISS04** (H. Yamada et al., Nucl. Fusion **45** (2005) 1684):
  `τ_E = 0.134 a^2.28 R^0.64 P^−0.61 n₁₉^0.54 B^0.84 ι_{2/3}^0.41` (s; m, MW, 10¹⁹ m⁻³, T).
  `StellaratorParams.iss04`.

At fixed machine parameters both reduce to `τ_E = H · C · (P / 1 MW)^(−α)`
(`ConfinementLaw.tau`), with a machine coefficient `C > 0` and a power-degradation exponent
`0 < α < 1`. The confinement-enhancement factor `H` is uncertain and is only assumed to lie
in a range `[H_lo, H_hi]`, possibly varying in time.

## Which power `P`? (two explicit conventions)

* `SteadyScaling`: `P(t) = P_α(T(t)) + P_aux(t)`, the instantaneous **heating** power.
  This is the usual steady-state approximation (at a steady state `dW/dt = 0`, and radiation
  is not subtracted).
* `LossScaling`: `P(t) = P_L(t) = P_α + P_aux − dW/dt`, the **loss power** of the ITER
  database definition `τ_E = W / P_L` (radiation not subtracted). Here `P_L` is a separate
  function tied to the trajectory by its derivative. Under the kernel balance law it equals
  `P_br + W/τ_E` (`LossScaling.loss_eq`), so `τ_E = H C (P_br + W/τ_E)^(−α)` is an
  *implicit*, but non-circular, relation between `τ_E` and the state `T`.

## Main argument

Write `y = P/1 MW` and `G(y) = 10⁶ y^(1−α) − P_br y^(−α)` (`scalingMargin`).
The steady-form net heating is
`P − P_br − W/τ(h, P) = y^α (G(y) − W/(h C))` (`steadyNet_eq`). `G` is increasing because
`α < 1` (`scalingMargin_mono`). Therefore **one** numeric inequality at the extreme data
(minimal heating power and `H_lo` at `T_lo`; maximal heating power and `H_hi` at `T_hi`)
controls the sign of the net heating for **all** admissible powers and `H`
(`steadyNet_pos_of_le`, `steadyNet_neg_of_le`). The power degradation `α > 0` is what makes
the upper barrier possible.

For the loss-power form, the identity `P_L = P_br + W/τ` makes the steady-form net heating
*vanish* at `P = P_L`. If the true heating rate `dW/dt = P_heat − P_L` had the wrong sign at a
crossing, then `P_L` would lie on the side where the steady-form net heating has a strict
sign, which is a contradiction (`LossScaling.lower_crossing`, `upper_crossing`). So the same
numeric certificate serves both conventions.

`le_rpow_of_pow_le` and `rpow_le_of_le_pow` convert real-exponent bounds `x^(a/b)` into
integer-power inequalities `l^b ≤ x^a`, which `norm_num` checks exactly.
-/

public section
noncomputable section

namespace PlasmaLean.Fusion

open DTPlasma

/-! ### Rational bracketing of real powers -/

/-- Lower bound for a rational real power: if `l^b ≤ x^a` (`l, x ≥ 0`, `b ≠ 0`) then
`l ≤ x^(a/b)`. -/
theorem le_rpow_of_pow_le {l x : ℝ} {a b : ℕ} (hb : b ≠ 0) (hl : 0 ≤ l) (hx : 0 ≤ x)
    (h : l ^ b ≤ x ^ a) : l ≤ x ^ ((a : ℝ) / b) := by
  have h1 : x ^ ((a : ℝ) / b) = (x ^ a) ^ ((b : ℝ)⁻¹) := by
    rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
  calc l = (l ^ b) ^ ((b : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hl hb).symm
    _ ≤ (x ^ a) ^ ((b : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = _ := h1.symm

/-- Upper bound for a rational real power: if `x^a ≤ u^b` (`u, x ≥ 0`, `b ≠ 0`) then
`x^(a/b) ≤ u`. -/
theorem rpow_le_of_le_pow {u x : ℝ} {a b : ℕ} (hb : b ≠ 0) (hu : 0 ≤ u) (hx : 0 ≤ x)
    (h : x ^ a ≤ u ^ b) : x ^ ((a : ℝ) / b) ≤ u := by
  have h1 : x ^ ((a : ℝ) / b) = (x ^ a) ^ ((b : ℝ)⁻¹) := by
    rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
  calc x ^ ((a : ℝ) / b) = (x ^ a) ^ ((b : ℝ)⁻¹) := h1
    _ ≤ (u ^ b) ^ ((b : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = u := Real.pow_rpow_inv_natCast hu hb

/-! ### Power-law confinement scalings -/

/-- A power-law confinement scaling at fixed machine parameters:
`τ_E = H · C · (P / 1 MW)^(−α)` with coefficient `C` (s · MW^α) and exponent `α`. -/
structure ConfinementLaw where
  /-- Machine coefficient (all non-power factors of the fit), s · MW^α. -/
  C : ℝ
  /-- Power-degradation exponent. -/
  α : ℝ

/-- Admissibility of a scaling law: `C > 0` and `0 < α < 1` (true for IPB98(y,2),
`α = 0.69`, and ISS04, `α = 0.61`). -/
class ConfinementLaw.Admissible (L : ConfinementLaw) : Prop where
  C_pos : 0 < L.C
  α_pos : 0 < L.α
  α_lt_one : L.α < 1

/-- Confinement time (s) predicted by the law at enhancement factor `H` and power `P` (W). -/
@[expose] def ConfinementLaw.tau (L : ConfinementLaw) (H P : ℝ) : ℝ :=
  H * L.C * (P / 1e6) ^ (-L.α)

/-- Machine parameters for the IPB98(y,2) tokamak scaling: plasma current `Ip` (MA),
toroidal field `B` (T), line-averaged density `n19` (10¹⁹ m⁻³), ion mass `M` (amu), major
radius `R` (m), inverse aspect ratio `eps = a/R`, area elongation `kappa`. -/
structure TokamakParams where
  /-- Plasma current, MA. -/
  Ip : ℝ
  /-- Toroidal field, T. -/
  B : ℝ
  /-- Line-averaged density, 10¹⁹ m⁻³. -/
  n19 : ℝ
  /-- Average ion mass, amu. -/
  M : ℝ
  /-- Major radius, m. -/
  R : ℝ
  /-- Inverse aspect ratio `a/R`. -/
  eps : ℝ
  /-- Area elongation `κ_a`. -/
  kappa : ℝ

/-- IPB98(y,2) machine coefficient
`0.0562 I_p^0.93 B^0.15 n₁₉^0.41 M^0.19 R^1.97 ε^0.58 κ^0.78` (ITER Physics Basis 1999). -/
@[expose] def TokamakParams.ipb98Coeff (q : TokamakParams) : ℝ :=
  0.0562 * q.Ip ^ (0.93 : ℝ) * q.B ^ (0.15 : ℝ) * q.n19 ^ (0.41 : ℝ) * q.M ^ (0.19 : ℝ) *
    q.R ^ (1.97 : ℝ) * q.eps ^ (0.58 : ℝ) * q.kappa ^ (0.78 : ℝ)

/-- The IPB98(y,2) law for given tokamak parameters (`α = 0.69`). -/
@[expose] def TokamakParams.ipb98 (q : TokamakParams) : ConfinementLaw :=
  ⟨q.ipb98Coeff, 0.69⟩

/-- Sanity: the IPB98(y,2) law written out in full (P in W, converted to MW). -/
theorem TokamakParams.ipb98_tau (q : TokamakParams) (H P : ℝ) :
    q.ipb98.tau H P = 0.0562 * H * q.Ip ^ (0.93 : ℝ) * q.B ^ (0.15 : ℝ) *
      (P / 1e6) ^ (-0.69 : ℝ) * q.n19 ^ (0.41 : ℝ) * q.M ^ (0.19 : ℝ) * q.R ^ (1.97 : ℝ) *
      q.eps ^ (0.58 : ℝ) * q.kappa ^ (0.78 : ℝ) := by
  simp only [ConfinementLaw.tau, ipb98, ipb98Coeff]; ring

/-- Positive tokamak parameters give an admissible IPB98(y,2) law. -/
theorem TokamakParams.ipb98_admissible (q : TokamakParams) (h1 : 0 < q.Ip) (h2 : 0 < q.B)
    (h3 : 0 < q.n19) (h4 : 0 < q.M) (h5 : 0 < q.R) (h6 : 0 < q.eps) (h7 : 0 < q.kappa) :
    q.ipb98.Admissible where
  C_pos := by simp only [ipb98, ipb98Coeff]; positivity
  α_pos := by norm_num [ipb98]
  α_lt_one := by norm_num [ipb98]

/-- Machine parameters for the ISS04 stellarator scaling: minor radius `a` (m), major
radius `R` (m), field `B` (T), density `n19` (10¹⁹ m⁻³), rotational transform `iota` at
two-thirds radius. -/
structure StellaratorParams where
  /-- Minor radius, m. -/
  a : ℝ
  /-- Major radius, m. -/
  R : ℝ
  /-- Magnetic field, T. -/
  B : ℝ
  /-- Line-averaged density, 10¹⁹ m⁻³. -/
  n19 : ℝ
  /-- Rotational transform `ι(2/3)`. -/
  iota : ℝ

/-- ISS04 machine coefficient `0.134 a^2.28 R^0.64 n₁₉^0.54 B^0.84 ι^0.41`
(Yamada et al., Nucl. Fusion 45 (2005) 1684). -/
@[expose] def StellaratorParams.iss04Coeff (q : StellaratorParams) : ℝ :=
  0.134 * q.a ^ (2.28 : ℝ) * q.R ^ (0.64 : ℝ) * q.n19 ^ (0.54 : ℝ) * q.B ^ (0.84 : ℝ) *
    q.iota ^ (0.41 : ℝ)

/-- The ISS04 law for given stellarator parameters (`α = 0.61`). -/
@[expose] def StellaratorParams.iss04 (q : StellaratorParams) : ConfinementLaw :=
  ⟨q.iss04Coeff, 0.61⟩

/-- Positive stellarator parameters give an admissible ISS04 law. -/
theorem StellaratorParams.iss04_admissible (q : StellaratorParams) (h1 : 0 < q.a)
    (h2 : 0 < q.R) (h3 : 0 < q.B) (h4 : 0 < q.n19) (h5 : 0 < q.iota) :
    q.iss04.Admissible where
  C_pos := by simp only [iss04, iss04Coeff]; positivity
  α_pos := by norm_num [iss04]
  α_lt_one := by norm_num [iss04]

namespace ConfinementLaw

variable (L : ConfinementLaw) [L.Admissible]

/-- The predicted confinement time is positive for `H > 0` and `P > 0`. -/
theorem tau_pos {H P : ℝ} (hH : 0 < H) (hP : 0 < P) : 0 < L.tau H P :=
  mul_pos (mul_pos hH Admissible.C_pos) (Real.rpow_pos_of_pos (by positivity) _)

/-- **Power degradation.** For fixed `H > 0`, the predicted `τ_E` is strictly decreasing in
the power `P > 0`. -/
theorem tau_strictAntiOn {H : ℝ} (hH : 0 < H) : StrictAntiOn (L.tau H) (Set.Ioi 0) := by
  intro P₁ h₁ P₂ h₂ h12
  have h₁' : (0 : ℝ) < P₁ := h₁
  unfold tau
  have := Admissible.C_pos (L := L)
  have hα := Admissible.α_pos (L := L)
  have : (P₂ / 1e6) ^ (-L.α) < (P₁ / 1e6) ^ (-L.α) :=
    Real.rpow_lt_rpow_of_neg (by positivity) (by linarith) (by linarith)
  exact mul_lt_mul_of_pos_left this (by positivity)

/-- The predicted `τ_E` is increasing in the enhancement factor `H` (at `P > 0`). -/
theorem tau_mono_H {H₁ H₂ P : ℝ} (hP : 0 < P) (h : H₁ ≤ H₂) : L.tau H₁ P ≤ L.tau H₂ P := by
  unfold tau
  have := Admissible.C_pos (L := L)
  have : 0 < (P / 1e6) ^ (-L.α) := Real.rpow_pos_of_pos (by positivity) _
  gcongr

omit [L.Admissible] in
/-- Scaling of `τ_E` with power: multiplying `P` by `k > 0` multiplies `τ_E` by `k^(−α)`. -/
theorem tau_mul_power {H P k : ℝ} (hP : 0 < P) (hk : 0 < k) :
    L.tau H (k * P) = k ^ (-L.α) * L.tau H P := by
  unfold tau
  rw [mul_div_assoc, Real.mul_rpow hk.le (by positivity)]; ring

end ConfinementLaw

/-! ### The margin function and the steady-form net heating -/

/-- `G(y) = 10⁶ y^(1−α) − b y^(−α)` (`y` = power in MW, `b` = bremsstrahlung in W). -/
@[expose] def scalingMargin (α b y : ℝ) : ℝ := 1e6 * y ^ (1 - α) - b * y ^ (-α)

/-- `G` is nondecreasing on `y > 0` for `0 ≤ α ≤ 1`, `b ≥ 0`. -/
theorem scalingMargin_mono {α b y₁ y₂ : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hb : 0 ≤ b)
    (hy : 0 < y₁) (h : y₁ ≤ y₂) : scalingMargin α b y₁ ≤ scalingMargin α b y₂ := by
  have h1 := Real.rpow_le_rpow hy.le h (by linarith : 0 ≤ 1 - α)
  have h2 := Real.rpow_le_rpow_of_nonpos hy h (by linarith : -α ≤ 0)
  unfold scalingMargin
  nlinarith

/-- **Factorization of the steady-form net heating.** For `P, h, C > 0` and `y = P/10⁶`:
`P − b − W / (h C y^(−α)) = y^α (G(y) − W/(h C))`. -/
theorem steadyNet_eq (L : ConfinementLaw) [L.Admissible] {P b W h : ℝ} (hP : 0 < P)
    (hh : 0 < h) :
    P - b - W / L.tau h P =
      (P / 1e6) ^ L.α * (scalingMargin L.α b (P / 1e6) - W / (h * L.C)) := by
  have hC := ConfinementLaw.Admissible.C_pos (L := L)
  have hy : 0 < P / 1e6 := by positivity
  have hA : 0 < (P / 1e6) ^ L.α := Real.rpow_pos_of_pos hy _
  unfold scalingMargin ConfinementLaw.tau
  rw [Real.rpow_neg hy.le, Real.rpow_sub hy, Real.rpow_one]
  field_simp

/-- **Lower crossing, steady form.** If the steady-form net heating at the minimal heating
power `P_min` and the minimal enhancement factor `H_lo` is positive, then it is positive at
every heating power `P ≥ P_min` and every `h ≥ H_lo` (same `W ≥ 0`, `b ≥ 0`). -/
theorem steadyNet_pos_of_le (L : ConfinementLaw) [L.Admissible] {W b Pmin P Hlo h : ℝ}
    (hW : 0 ≤ W) (hb : 0 ≤ b) (hPmin : 0 < Pmin) (hP : Pmin ≤ P) (hH : 0 < Hlo)
    (hh : Hlo ≤ h) (hnum : 0 < Pmin - b - W / L.tau Hlo Pmin) :
    0 < P - b - W / L.tau h P := by
  have hC := ConfinementLaw.Admissible.C_pos (L := L)
  have hα0 := ConfinementLaw.Admissible.α_pos (L := L)
  have hα1 := ConfinementLaw.Admissible.α_lt_one (L := L)
  have hP0 : 0 < P := hPmin.trans_le hP
  rw [steadyNet_eq L hPmin hH] at hnum
  rw [steadyNet_eq L hP0 (hH.trans_le hh)]
  have hA0 : 0 < (Pmin / 1e6) ^ L.α := Real.rpow_pos_of_pos (by positivity) _
  have hA : 0 < (P / 1e6) ^ L.α := Real.rpow_pos_of_pos (by positivity) _
  have h1 : W / (Hlo * L.C) < scalingMargin L.α b (Pmin / 1e6) := by
    by_contra hc; rw [not_lt] at hc
    exact absurd hnum (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hA0.le (by linarith)))
  have h2 := scalingMargin_mono hα0.le hα1.le hb (by positivity : 0 < Pmin / 1e6)
    (div_le_div_of_nonneg_right hP (by norm_num))
  have h3 : W / (h * L.C) ≤ W / (Hlo * L.C) :=
    div_le_div_of_nonneg_left hW (by positivity) (by gcongr)
  exact mul_pos hA (by linarith)

/-- **Upper crossing, steady form.** If the steady-form net heating at the maximal heating
power `P_max` and the maximal enhancement factor `H_hi` is negative, then it is negative at
every heating power `0 < P ≤ P_max` and every `0 < h ≤ H_hi`. -/
theorem steadyNet_neg_of_le (L : ConfinementLaw) [L.Admissible] {W b Pmax P Hhi h : ℝ}
    (hW : 0 ≤ W) (hb : 0 ≤ b) (hP0 : 0 < P) (hP : P ≤ Pmax) (hh0 : 0 < h) (hh : h ≤ Hhi)
    (hnum : Pmax - b - W / L.tau Hhi Pmax < 0) :
    P - b - W / L.tau h P < 0 := by
  have hC := ConfinementLaw.Admissible.C_pos (L := L)
  have hα0 := ConfinementLaw.Admissible.α_pos (L := L)
  have hα1 := ConfinementLaw.Admissible.α_lt_one (L := L)
  have hPm : 0 < Pmax := hP0.trans_le hP
  have hH : 0 < Hhi := hh0.trans_le hh
  rw [steadyNet_eq L hPm hH] at hnum
  rw [steadyNet_eq L hP0 hh0]
  have hA0 : 0 < (Pmax / 1e6) ^ L.α := Real.rpow_pos_of_pos (by positivity) _
  have hA : 0 < (P / 1e6) ^ L.α := Real.rpow_pos_of_pos (by positivity) _
  have h1 : scalingMargin L.α b (Pmax / 1e6) < W / (Hhi * L.C) := by
    by_contra hc; rw [not_lt] at hc
    exact absurd hnum (not_lt.mpr (mul_nonneg hA0.le (by linarith)))
  have h2 := scalingMargin_mono hα0.le hα1.le hb (by positivity : 0 < P / 1e6)
    (div_le_div_of_nonneg_right hP (by norm_num))
  have h3 : W / (Hhi * L.C) ≤ W / (h * L.C) :=
    div_le_div_of_nonneg_left hW (by positivity) (by gcongr)
  exact mul_neg_of_pos_of_neg hA (by linarith)

/-! ### Scaling laws on trajectories -/

/-- **Supplied confinement scaling, steady (heating-power) form.** Along the trajectory, for
`t ≥ 0`: the enhancement factor `H(t)` lies in `[H_lo, H_hi]`, and
`τ_E(t) = H(t) · C · ((P_α(T(t)) + P_aux(t)) / 1 MW)^(−α)`.

The law is only meaningful for positive heating power (for `P ≤ 0`, Lean's `Real.rpow`
of a nonpositive base is a junk value). The field `P_pos` therefore requires
`P_α + P_aux > 0`. -/
class SteadyScaling (L : ConfinementLaw) (Hlo Hhi : ℝ) (p : DTPlasma)
    (sv Paux τE T H : ℝ → ℝ) : Prop where
  H_mem : ∀ t : ℝ, 0 ≤ t → H t ∈ Set.Icc Hlo Hhi
  tau_eq : ∀ t : ℝ, 0 ≤ t → τE t = L.tau (H t) (p.alphaPower sv (T t) + Paux t)
  P_pos : ∀ t : ℝ, 0 ≤ t → 0 < p.alphaPower sv (T t) + Paux t

/-- **Supplied confinement scaling, loss-power form** (ITER database convention
`τ_E = W/P_L`, `P_L = P_heat − dW/dt`, radiation not subtracted). `P_L(t)` is tied to the
trajectory by `d/dt W(T(t)) = P_α + P_aux − P_L(t)`, and
`τ_E(t) = H(t) · C · (P_L(t) / 1 MW)^(−α)` with `H(t) ∈ [H_lo, H_hi]`.

Domain caveat: the law needs `P_L > 0`. At `T = 0` the balance law gives
`P_L = W/τ_E + P_br = 0`, and Lean's `0^(−α) = 0` would force `τ_E = 0`, contradicting
`PowerBalance.tauE_pos`. The class together with `PowerBalance` is therefore
unsatisfiable by trajectories that reach `T = 0`. The field `PL_pos` states the intended
domain explicitly. -/
class LossScaling (L : ConfinementLaw) (Hlo Hhi : ℝ) (p : DTPlasma)
    (sv Paux τE T H PL : ℝ → ℝ) : Prop where
  H_mem : ∀ t : ℝ, 0 ≤ t → H t ∈ Set.Icc Hlo Hhi
  loss_deriv : ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt (fun s => p.thermalEnergy (T s))
      (p.alphaPower sv (T t) + Paux t - PL t) (Set.Ici 0) t
  tau_eq : ∀ t : ℝ, 0 ≤ t → τE t = L.tau (H t) (PL t)
  PL_pos : ∀ t : ℝ, 0 ≤ t → 0 < PL t

variable {L : ConfinementLaw} {Hlo Hhi : ℝ} {p : DTPlasma} {sv Paux τE T H PL : ℝ → ℝ}

/-- Bremsstrahlung is nonnegative. -/
theorem bremsPower_nonneg (p : DTPlasma) [PhysicalPlasma p] (x : ℝ) : 0 ≤ p.bremsPower x := by
  have := PhysicalPlasma.n_pos (p := p); have := PhysicalPlasma.V_pos (p := p)
  have : (0 : ℝ) ≤ p.Zeff := by linarith [PhysicalPlasma.Zeff_ge_one (p := p)]
  unfold bremsPower bremsCoeff; positivity

/-- Under the kernel balance law, the loss power of `LossScaling` is
`P_L = P_br + W/τ_E` (uniqueness of one-sided derivatives on `[0, ∞)`). -/
theorem LossScaling.loss_eq [PowerBalance p sv Paux τE T]
    [LossScaling L Hlo Hhi p sv Paux τE T H PL]
    {t : ℝ} (ht : 0 ≤ t) : PL t = p.bremsPower (T t) + p.lossPower (τE t) (T t) := by
  have h := (uniqueDiffOn_Ici (0 : ℝ) t ht).eq_deriv _
    (‹LossScaling L Hlo Hhi p sv Paux τE T H PL›.loss_deriv t ht)
    (‹PowerBalance p sv Paux τE T›.balance t ht)
  unfold netHeating at h; linarith

/-- **Lower crossing from the steady-form scaling law.** If at each crossing of `T_lo` the
heating power is at least `P_min > 0`, and the steady-form net heating at `(P_min, H_lo)` is
positive, then the actual net heating at every crossing is positive. -/
theorem SteadyScaling.lower_crossing [L.Admissible] [PhysicalPlasma p]
    [SteadyScaling L Hlo Hhi p sv Paux τE T H] {Tlo Pmin : ℝ} (hTlo : 0 ≤ Tlo)
    (hPmin : 0 < Pmin) (hHlo : 0 < Hlo)
    (hheat : ∀ t, 0 ≤ t → T t = Tlo → Pmin ≤ p.alphaPower sv Tlo + Paux t)
    (hnum : 0 < Pmin - p.bremsPower Tlo - p.lossPower (L.tau Hlo Pmin) Tlo) :
    ∀ t, 0 ≤ t → T t = Tlo → 0 < p.netHeating sv (Paux t) (τE t) Tlo := by
  intro t ht hT
  have hτ := ‹SteadyScaling L Hlo Hhi p sv Paux τE T H›.tau_eq t ht
  rw [hT] at hτ
  have hH := (‹SteadyScaling L Hlo Hhi p sv Paux τE T H›.H_mem t ht).1
  have := steadyNet_pos_of_le L (thermalEnergy_nonneg p hTlo) (bremsPower_nonneg p Tlo) hPmin
    (hheat t ht hT) hHlo hH hnum
  unfold netHeating lossPower; rw [hτ]; linarith

/-- **Upper crossing from the steady-form scaling law.** If at each crossing of `T_hi` the
heating power lies in `(0, P_max]`, and the steady-form net heating at `(P_max, H_hi)` is
negative, then the actual net heating at every crossing is negative (`H_lo > 0`). -/
theorem SteadyScaling.upper_crossing [L.Admissible] [PhysicalPlasma p]
    [SteadyScaling L Hlo Hhi p sv Paux τE T H] {Thi Pmax : ℝ} (hThi : 0 ≤ Thi)
    (hHlo : 0 < Hlo)
    (hpos : ∀ t, 0 ≤ t → T t = Thi → 0 < p.alphaPower sv Thi + Paux t)
    (hheat : ∀ t, 0 ≤ t → T t = Thi → p.alphaPower sv Thi + Paux t ≤ Pmax)
    (hnum : Pmax - p.bremsPower Thi - p.lossPower (L.tau Hhi Pmax) Thi < 0) :
    ∀ t, 0 ≤ t → T t = Thi → p.netHeating sv (Paux t) (τE t) Thi < 0 := by
  intro t ht hT
  have hτ := ‹SteadyScaling L Hlo Hhi p sv Paux τE T H›.tau_eq t ht
  rw [hT] at hτ
  have hH := ‹SteadyScaling L Hlo Hhi p sv Paux τE T H›.H_mem t ht
  have := steadyNet_neg_of_le L (thermalEnergy_nonneg p hThi) (bremsPower_nonneg p Thi)
    (hpos t ht hT) (hheat t ht hT) (hHlo.trans_le hH.1) hH.2 hnum
  unfold netHeating lossPower; rw [hτ]; linarith

/-- **Lower crossing from the loss-power scaling law.** Same numeric hypothesis as the
steady form. Proof: if `dW/dt ≤ 0` at a crossing then `P_L ≥ P_heat ≥ P_min`, while
`P_L = P_br + W/τ_E(P_L)` makes the steady-form net heating at `P_L` vanish, contradicting
`steadyNet_pos_of_le`. -/
theorem LossScaling.lower_crossing [L.Admissible] [PhysicalPlasma p]
    [PowerBalance p sv Paux τE T] [LossScaling L Hlo Hhi p sv Paux τE T H PL] {Tlo Pmin : ℝ}
    (hTlo : 0 ≤ Tlo) (hPmin : 0 < Pmin) (hHlo : 0 < Hlo)
    (hheat : ∀ t, 0 ≤ t → T t = Tlo → Pmin ≤ p.alphaPower sv Tlo + Paux t)
    (hnum : 0 < Pmin - p.bremsPower Tlo - p.lossPower (L.tau Hlo Pmin) Tlo) :
    ∀ t, 0 ≤ t → T t = Tlo → 0 < p.netHeating sv (Paux t) (τE t) Tlo := by
  intro t ht hT
  have hL := LossScaling.loss_eq (L := L) (Hlo := Hlo) (Hhi := Hhi) (H := H) (PL := PL) (sv := sv)
    (Paux := Paux) (τE := τE) (T := T) (p := p) ht
  have hτ := ‹LossScaling L Hlo Hhi p sv Paux τE T H PL›.tau_eq t ht
  have hH := (‹LossScaling L Hlo Hhi p sv Paux τE T H PL›.H_mem t ht).1
  rw [hT] at hL
  by_contra hneg
  rw [not_lt] at hneg
  have hPL : Pmin ≤ PL t := by
    have := hheat t ht hT; unfold netHeating at hneg; linarith
  have hpos := steadyNet_pos_of_le L (thermalEnergy_nonneg p hTlo) (bremsPower_nonneg p Tlo)
    hPmin hPL hHlo hH hnum
  rw [← hτ] at hpos
  unfold lossPower at hL; linarith

/-- **Upper crossing from the loss-power scaling law.** Same numeric hypothesis as the
steady form (`T_hi > 0`, `H_lo > 0`). If `dW/dt ≥ 0` at a crossing then
`0 < P_L ≤ P_heat ≤ P_max`, contradicting `steadyNet_neg_of_le` at `P = P_L`. -/
theorem LossScaling.upper_crossing [L.Admissible] [PhysicalPlasma p]
    [PowerBalance p sv Paux τE T] [LossScaling L Hlo Hhi p sv Paux τE T H PL] {Thi Pmax : ℝ}
    (hThi : 0 < Thi) (hHlo : 0 < Hlo)
    (hheat : ∀ t, 0 ≤ t → T t = Thi → p.alphaPower sv Thi + Paux t ≤ Pmax)
    (hnum : Pmax - p.bremsPower Thi - p.lossPower (L.tau Hhi Pmax) Thi < 0) :
    ∀ t, 0 ≤ t → T t = Thi → p.netHeating sv (Paux t) (τE t) Thi < 0 := by
  intro t ht hT
  have hL := LossScaling.loss_eq (L := L) (Hlo := Hlo) (Hhi := Hhi) (H := H) (PL := PL) (sv := sv)
    (Paux := Paux) (τE := τE) (T := T) (p := p) ht
  have hτ := ‹LossScaling L Hlo Hhi p sv Paux τE T H PL›.tau_eq t ht
  have hH := ‹LossScaling L Hlo Hhi p sv Paux τE T H PL›.H_mem t ht
  have hτpos := ‹PowerBalance p sv Paux τE T›.tauE_pos t ht
  rw [hT] at hL
  have hWpos : 0 < p.thermalEnergy Thi := by
    rw [thermalEnergy_eq]; exact mul_pos (heatCapacity_pos p) hThi
  have hPL0 : 0 < PL t := by
    rw [hL]; unfold lossPower
    linarith [bremsPower_nonneg p Thi, div_pos hWpos hτpos]
  by_contra hneg
  rw [not_lt] at hneg
  have hPL : PL t ≤ Pmax := by
    have := hheat t ht hT; unfold netHeating at hneg; linarith
  have hnegs := steadyNet_neg_of_le L (thermalEnergy_nonneg p hThi.le)
    (bremsPower_nonneg p Thi) hPL0 hPL (hHlo.trans_le hH.1) hH.2 hnum
  rw [← hτ] at hnegs
  unfold lossPower at hL; linarith

/-- **Burn window from the steady-form scaling law.** Both numeric crossing certificates
give `T(t) ∈ [T_lo, T_hi]` for all `t ≥ 0`. -/
theorem SteadyScaling.window [L.Admissible] [PhysicalPlasma p] [PowerBalance p sv Paux τE T]
    [SteadyScaling L Hlo Hhi p sv Paux τE T H] {Tlo Thi Pmin Pmax : ℝ} (hTlo : 0 ≤ Tlo)
    (hThi : 0 ≤ Thi) (hPmin : 0 < Pmin) (hHlo : 0 < Hlo)
    (hheatlo : ∀ t, 0 ≤ t → T t = Tlo → Pmin ≤ p.alphaPower sv Tlo + Paux t)
    (hpos : ∀ t, 0 ≤ t → T t = Thi → 0 < p.alphaPower sv Thi + Paux t)
    (hheathi : ∀ t, 0 ≤ t → T t = Thi → p.alphaPower sv Thi + Paux t ≤ Pmax)
    (hnumlo : 0 < Pmin - p.bremsPower Tlo - p.lossPower (L.tau Hlo Pmin) Tlo)
    (hnumhi : Pmax - p.bremsPower Thi - p.lossPower (L.tau Hhi Pmax) Thi < 0)
    (h0 : T 0 ∈ Set.Icc Tlo Thi) : ∀ t, 0 ≤ t → T t ∈ Set.Icc Tlo Thi :=
  PowerBalance.window h0
    (SteadyScaling.lower_crossing (L := L) (τE := τE) (Hhi := Hhi) (H := H) hTlo hPmin hHlo hheatlo
      hnumlo)
    (SteadyScaling.upper_crossing (L := L) (τE := τE) (Hlo := Hlo) (H := H) hThi hHlo hpos hheathi
      hnumhi)

/-- **Burn window from the loss-power scaling law.** Same certificates as `SteadyScaling.window`
(here `T_hi > 0`, and no positivity hypothesis on the heating power is needed). -/
theorem LossScaling.window [L.Admissible] [PhysicalPlasma p] [PowerBalance p sv Paux τE T]
    [LossScaling L Hlo Hhi p sv Paux τE T H PL] {Tlo Thi Pmin Pmax : ℝ} (hTlo : 0 ≤ Tlo)
    (hThi : 0 < Thi) (hPmin : 0 < Pmin) (hHlo : 0 < Hlo)
    (hheatlo : ∀ t, 0 ≤ t → T t = Tlo → Pmin ≤ p.alphaPower sv Tlo + Paux t)
    (hheathi : ∀ t, 0 ≤ t → T t = Thi → p.alphaPower sv Thi + Paux t ≤ Pmax)
    (hnumlo : 0 < Pmin - p.bremsPower Tlo - p.lossPower (L.tau Hlo Pmin) Tlo)
    (hnumhi : Pmax - p.bremsPower Thi - p.lossPower (L.tau Hhi Pmax) Thi < 0)
    (h0 : T 0 ∈ Set.Icc Tlo Thi) : ∀ t, 0 ≤ t → T t ∈ Set.Icc Tlo Thi :=
  PowerBalance.window h0
    (LossScaling.lower_crossing (L := L) (τE := τE) (Hhi := Hhi) (H := H) (PL := PL) hTlo
      hPmin hHlo hheatlo hnumlo)
    (LossScaling.upper_crossing (L := L) (τE := τE) (Hlo := Hlo) (H := H) (PL := PL) hThi
      hHlo hheathi hnumhi)

end PlasmaLean.Fusion
