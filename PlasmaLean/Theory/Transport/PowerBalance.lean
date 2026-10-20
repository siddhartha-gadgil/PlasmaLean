/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Kernel.Fusion
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Invariant temperature windows for the 0-D D-T power balance

Track T4 of `notes/implementation-plan.md`.

1. **Generic scalar barriers** (`PlasmaLean.Transport`): if a differentiable scalar
   `f` on `[0, ∞)` satisfies `f' t > 0` whenever `f t = a`, then `f 0 ≥ a` implies
   `f t ≥ a` for all `t ≥ 0` (a lower barrier). The proof is Mathlib's fencing
   theorem `image_le_of_deriv_right_lt_deriv_boundary`
   (`Mathlib/Analysis/Calculus/MeanValue.lean`). Symmetric upper barriers and
   invariant windows follow, also in the ODE form `f' = G(t, f)`.
2. **Burn theorems** (`PlasmaLean.Fusion`): for a trajectory satisfying the kernel law
   `PowerBalance`, positive net heating at `T_lo` (resp. negative at `T_hi`) at every
   crossing time gives `T(t) ≥ T_lo` (resp. `≤ T_hi`) for all `t ≥ 0`. Comparison
   lemmas reduce the crossing conditions to single numeric inequalities using lower
   bounds on `⟨σv⟩`, `P_aux`, `τ_E` (or upper bounds for the upper barrier).
3. **Conditional burn yield**: if `T(t)` stays in a window `[T_lo, T_hi] ⊆ [1, 60]` keV
   on `[0, t_b]`, monotonicity of the supplied reactivity gives
   `∫₀^{t_b} P_fus(T(t)) dt ≥ P_fus(T_lo) · t_b`.

No existence of solutions is asserted: all results are about supplied trajectories.
-/

public section
noncomputable section

namespace PlasmaLean

namespace Transport

/-- **Lower barrier.** If `f` is differentiable on `[0, ∞)` (derivative within `[0, ∞)`,
one-sided at `0`) with `f' t > 0` whenever `f t = a`, then `a ≤ f 0` implies `a ≤ f t`
for all `t ≥ 0`. -/
theorem lower_barrier {f f' : ℝ → ℝ} {a : ℝ}
    (hf : ∀ t, 0 ≤ t → HasDerivWithinAt f (f' t) (Set.Ici 0) t) (h0 : a ≤ f 0)
    (hcross : ∀ t, 0 ≤ t → f t = a → 0 < f' t) : ∀ t, 0 ≤ t → a ≤ f t := by
  intro t ht
  have key := image_le_of_deriv_right_lt_deriv_boundary (f := fun s => -f s)
    (f' := fun s => -f' s) (a := 0) (b := t) (B := fun _ => -a) (B' := fun _ => 0)
    (fun s hs => ((hf s hs.1).continuousWithinAt.mono Set.Icc_subset_Ici_self).neg)
    (fun s hs => ((hf s hs.1).mono (Set.Ici_subset_Ici.mpr hs.1)).neg) (show -f 0 ≤ -a by linarith)
    (fun _ => hasDerivAt_const _ _)
    (fun s hs heq => by have := hcross s hs.1 (by linarith); change -f' s < 0; linarith)
    ⟨ht, le_rfl⟩
  have key' : -f t ≤ -a := key
  linarith

/-- **Upper barrier.** If `f' t < 0` whenever `f t = b`, then `f 0 ≤ b` implies
`f t ≤ b` for all `t ≥ 0`. -/
theorem upper_barrier {f f' : ℝ → ℝ} {b : ℝ}
    (hf : ∀ t, 0 ≤ t → HasDerivWithinAt f (f' t) (Set.Ici 0) t) (h0 : f 0 ≤ b)
    (hcross : ∀ t, 0 ≤ t → f t = b → f' t < 0) : ∀ t, 0 ≤ t → f t ≤ b := by
  intro t ht
  have := lower_barrier (f := fun s => -f s) (f' := fun s => -f' s) (a := -b)
    (fun s hs => (hf s hs).neg) (show -b ≤ -f 0 by linarith)
    (fun s hs heq => by have := hcross s hs (by linarith); change 0 < -f' s; linarith) t ht
  have h' : -b ≤ -f t := this
  linarith

/-- **Invariant window.** Combining both barriers: `f t ∈ [a, b]` for all `t ≥ 0`. -/
theorem window_invariant {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t, 0 ≤ t → HasDerivWithinAt f (f' t) (Set.Ici 0) t) (h0 : f 0 ∈ Set.Icc a b)
    (hlo : ∀ t, 0 ≤ t → f t = a → 0 < f' t) (hhi : ∀ t, 0 ≤ t → f t = b → f' t < 0) :
    ∀ t, 0 ≤ t → f t ∈ Set.Icc a b :=
  fun t ht => ⟨lower_barrier hf h0.1 hlo t ht, upper_barrier hf h0.2 hhi t ht⟩

/-- Lower barrier in ODE form: `f' = G(t, f)` and `G(t, a) > 0` for all `t ≥ 0`. -/
theorem lower_barrier_ode {f : ℝ → ℝ} {G : ℝ → ℝ → ℝ} {a : ℝ}
    (hf : ∀ t, 0 ≤ t → HasDerivWithinAt f (G t (f t)) (Set.Ici 0) t) (h0 : a ≤ f 0)
    (hG : ∀ t, 0 ≤ t → 0 < G t a) : ∀ t, 0 ≤ t → a ≤ f t :=
  lower_barrier hf h0 (fun t ht heq => heq ▸ hG t ht)

/-- Upper barrier in ODE form: `f' = G(t, f)` and `G(t, b) < 0` for all `t ≥ 0`. -/
theorem upper_barrier_ode {f : ℝ → ℝ} {G : ℝ → ℝ → ℝ} {b : ℝ}
    (hf : ∀ t, 0 ≤ t → HasDerivWithinAt f (G t (f t)) (Set.Ici 0) t) (h0 : f 0 ≤ b)
    (hG : ∀ t, 0 ≤ t → G t b < 0) : ∀ t, 0 ≤ t → f t ≤ b :=
  upper_barrier hf h0 (fun t ht heq => heq ▸ hG t ht)

/-- Sanity corollary: the trivial ODE `f' = 1` started at `0` stays nonnegative. -/
theorem lower_barrier_sanity_id : ∀ t, 0 ≤ t → (0 : ℝ) ≤ id t :=
  lower_barrier_ode (G := fun _ _ => 1) (fun t _ => (hasDerivAt_id t).hasDerivWithinAt) le_rfl
    (fun _ _ => one_pos)

end Transport

namespace Fusion

open DTPlasma

variable {p : DTPlasma} {sv Paux τE T : ℝ → ℝ}

/-- Heat capacity `(3/2) n (1 + r_i) keV V` in J/keV. -/
@[expose] def heatCapacity (p : DTPlasma) : ℝ := 3 / 2 * p.n * (1 + p.ionRatio) * keV * p.V

/-- The thermal energy is linear in temperature with slope `heatCapacity`. -/
theorem thermalEnergy_eq (p : DTPlasma) (x : ℝ) :
    p.thermalEnergy x = heatCapacity p * x := by
  unfold thermalEnergy heatCapacity; ring

/-- The heat capacity of a physical plasma is positive. -/
theorem heatCapacity_pos (p : DTPlasma) [PhysicalPlasma p] : 0 < heatCapacity p := by
  have := PhysicalPlasma.n_pos (p := p); have := PhysicalPlasma.V_pos (p := p)
  have : 0 < 1 + p.ionRatio := by
    linarith [PhysicalPlasma.fuel_pos (p := p), PhysicalPlasma.fuel_le_ions (p := p)]
  unfold heatCapacity keV; positivity

/-- Thermal energy is nonnegative at nonnegative temperature. -/
theorem thermalEnergy_nonneg (p : DTPlasma) [PhysicalPlasma p] {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ p.thermalEnergy x := by
  rw [thermalEnergy_eq]; exact mul_nonneg (heatCapacity_pos p).le hx

/-- For `t > 0` the one-sided balance law gives an ordinary derivative. -/
theorem PowerBalance.hasDerivAt [PowerBalance p sv Paux τE T] {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => p.thermalEnergy (T s)) (p.netHeating sv (Paux t) (τE t) (T t)) t :=
  (PowerBalance.balance t ht.le).hasDerivAt (Ici_mem_nhds ht)

/-- Under the balance law, the temperature itself is differentiable within `[0, ∞)` at
every `t ≥ 0`, with `dT/dt = (net heating)/heatCapacity`. -/
theorem PowerBalance.temperature_hasDerivAt [PhysicalPlasma p] [PowerBalance p sv Paux τE T]
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt T (p.netHeating sv (Paux t) (τE t) (T t) / heatCapacity p)
      (Set.Ici 0) t := by
  have hc := (heatCapacity_pos p).ne'
  have h := (PowerBalance.balance (p := p) (sv := sv) (Paux := Paux) (τE := τE) (T := T)
    t ht).div_const
    (heatCapacity p)
  have hT : (fun s => p.thermalEnergy (T s) / (heatCapacity p)) = T := by
    funext s; rw [thermalEnergy_eq, mul_div_cancel_left₀ _ hc]
  rwa [hT] at h

/-- For `t > 0` the temperature has an ordinary derivative `(net heating)/heatCapacity`. -/
theorem PowerBalance.temperature_hasDerivAt_of_pos [PhysicalPlasma p]
    [PowerBalance p sv Paux τE T] {t : ℝ} (ht : 0 < t) :
    HasDerivAt T (p.netHeating sv (Paux t) (τE t) (T t) / heatCapacity p) t :=
  (PowerBalance.temperature_hasDerivAt (p := p) (sv := sv) (Paux := Paux) (τE := τE)
    ht.le).hasDerivAt (Ici_mem_nhds ht)

/-- Under the balance law the temperature is continuous on `[0, ∞)` at every `t ≥ 0`. -/
theorem PowerBalance.continuousWithinAt [PhysicalPlasma p] [PowerBalance p sv Paux τE T]
    {t : ℝ} (ht : 0 ≤ t) : ContinuousWithinAt T (Set.Ici 0) t :=
  (PowerBalance.temperature_hasDerivAt (p := p) (sv := sv) (Paux := Paux) (τE := τE)
    ht).continuousWithinAt

/-- **Sustained burn (lower barrier).** If net heating is positive at every time at
which the temperature equals `T_lo`, then `T(0) ≥ T_lo` implies `T(t) ≥ T_lo` for all
`t ≥ 0`. -/
theorem PowerBalance.lower_barrier [PhysicalPlasma p] [PowerBalance p sv Paux τE T]
    {Tlo : ℝ} (h0 : Tlo ≤ T 0)
    (hcross : ∀ t, 0 ≤ t → T t = Tlo → 0 < p.netHeating sv (Paux t) (τE t) Tlo) :
    ∀ t, 0 ≤ t → Tlo ≤ T t := by
  have hc := heatCapacity_pos p
  intro t ht
  have := Transport.lower_barrier (f := fun s => p.thermalEnergy (T s))
    (a := (heatCapacity p) * Tlo) (fun s hs => PowerBalance.balance s hs)
    (by simp only [thermalEnergy_eq]; gcongr)
    (fun s hs heq => by
      have hTs : T s = Tlo := by
        simp only [thermalEnergy_eq] at heq
        exact mul_left_cancel₀ hc.ne' heq
      simpa [hTs] using hcross s hs hTs) t ht
  simp only [thermalEnergy_eq] at this
  exact le_of_mul_le_mul_left this hc

/-- **No thermal runaway (upper barrier).** If net heating is negative at every time
at which `T = T_hi`, then `T(0) ≤ T_hi` implies `T(t) ≤ T_hi` for all `t ≥ 0`. -/
theorem PowerBalance.upper_barrier [PhysicalPlasma p] [PowerBalance p sv Paux τE T]
    {Thi : ℝ} (h0 : T 0 ≤ Thi)
    (hcross : ∀ t, 0 ≤ t → T t = Thi → p.netHeating sv (Paux t) (τE t) Thi < 0) :
    ∀ t, 0 ≤ t → T t ≤ Thi := by
  have hc := heatCapacity_pos p
  intro t ht
  have := Transport.upper_barrier (f := fun s => p.thermalEnergy (T s))
    (b := (heatCapacity p) * Thi) (fun s hs => PowerBalance.balance s hs)
    (by simp only [thermalEnergy_eq]; gcongr)
    (fun s hs heq => by
      have hTs : T s = Thi := by
        simp only [thermalEnergy_eq] at heq
        exact mul_left_cancel₀ hc.ne' heq
      simpa [hTs] using hcross s hs hTs) t ht
  simp only [thermalEnergy_eq] at this
  exact le_of_mul_le_mul_left this hc

/-- **Burn window.** Both crossing conditions give `T(t) ∈ [T_lo, T_hi]` for all `t ≥ 0`. -/
theorem PowerBalance.window [PhysicalPlasma p] [PowerBalance p sv Paux τE T]
    {Tlo Thi : ℝ} (h0 : T 0 ∈ Set.Icc Tlo Thi)
    (hlo : ∀ t, 0 ≤ t → T t = Tlo → 0 < p.netHeating sv (Paux t) (τE t) Tlo)
    (hhi : ∀ t, 0 ≤ t → T t = Thi → p.netHeating sv (Paux t) (τE t) Thi < 0) :
    ∀ t, 0 ≤ t → T t ∈ Set.Icc Tlo Thi := fun t ht =>
  ⟨PowerBalance.lower_barrier h0.1 hlo t ht, PowerBalance.upper_barrier h0.2 hhi t ht⟩

/-- **Comparison, lower side.** Net heating at temperature `x ≥ 0` is at least the net
heating computed with a constant reactivity lower bound `s ≤ ⟨σv⟩(x)`, auxiliary
power lower bound `P ≤ P_aux`, and confinement-time lower bound `0 < τ ≤ τ_E`. -/
theorem netHeating_ge [PhysicalPlasma p] {s P τ Paux' τE' x : ℝ} (hx : 0 ≤ x)
    (hs : s ≤ sv x) (hP : P ≤ Paux') (hτ : 0 < τ) (hττ : τ ≤ τE') :
    p.netHeating (fun _ => s) P τ x ≤ p.netHeating sv Paux' τE' x := by
  have := PhysicalPlasma.n_pos (p := p); have := PhysicalPlasma.V_pos (p := p)
  have hW := thermalEnergy_nonneg p hx
  have hα : p.alphaPower (fun _ => s) x ≤ p.alphaPower sv x := by
    unfold alphaPower alphaEnergy keV; gcongr
  have hl : p.lossPower τE' x ≤ p.lossPower τ x := by
    unfold lossPower; exact div_le_div_of_nonneg_left hW hτ hττ
  unfold netHeating; linarith

/-- **Comparison, upper side.** Net heating at `x ≥ 0` is at most the net heating with
reactivity upper bound `⟨σv⟩(x) ≤ s`, `P_aux ≤ P` and `0 < τ_E ≤ τ`. -/
theorem netHeating_le [PhysicalPlasma p] {s P τ Paux' τE' x : ℝ} (hx : 0 ≤ x)
    (hs : sv x ≤ s) (hP : Paux' ≤ P) (hτ : 0 < τE') (hττ : τE' ≤ τ) :
    p.netHeating sv Paux' τE' x ≤ p.netHeating (fun _ => s) P τ x := by
  have := PhysicalPlasma.n_pos (p := p); have := PhysicalPlasma.V_pos (p := p)
  have hW := thermalEnergy_nonneg p hx
  have hα : p.alphaPower sv x ≤ p.alphaPower (fun _ => s) x := by
    unfold alphaPower alphaEnergy keV; gcongr
  have hl : p.lossPower τ x ≤ p.lossPower τE' x := by
    unfold lossPower; exact div_le_div_of_nonneg_left hW hτ hττ
  unfold netHeating; linarith

/-- Reading a supplied Bosch–Hale enclosure: if `w ∈ boschHaleWindows` and
`T ∈ [w.lo, w.hi]` then `w.svLo ≤ ⟨σv⟩(T) ≤ w.svHi`. -/
theorem BoschHaleDT.bounds (sv : ℝ → ℝ) [BoschHaleDT sv] {w : ReactivityWindow}
    (hw : w ∈ boschHaleWindows) {x : ℝ} (h1 : (w.lo : ℝ) ≤ x) (h2 : x ≤ w.hi) :
    (w.svLo : ℝ) ≤ sv x ∧ sv x ≤ w.svHi :=
  BoschHaleDT.windows w hw x h1 h2

/-- Window access by index into `boschHaleWindows`. -/
theorem BoschHaleDT.bounds_idx (sv : ℝ → ℝ) [BoschHaleDT sv] (i : ℕ)
    (hi : i < boschHaleWindows.length) {x : ℝ} (h1 : ((boschHaleWindows[i]).lo : ℝ) ≤ x)
    (h2 : x ≤ (boschHaleWindows[i]).hi) :
    ((boschHaleWindows[i]).svLo : ℝ) ≤ sv x ∧ sv x ≤ (boschHaleWindows[i]).svHi :=
  BoschHaleDT.bounds sv (List.getElem_mem hi) h1 h2

/-- **Sustained burn from numeric data.** Suppose `T_lo ≥ 0`, `s ≤ ⟨σv⟩(T_lo)`, and at
each crossing time of `T_lo` we have `P_aux ≥ P_min` and `τ_E ≥ τ* > 0`. If the single
numeric inequality `netHeating (const s) P_min τ* T_lo > 0` holds, then `T(t) ≥ T_lo`
for all `t ≥ 0` (under the `PowerBalance` hypotheses). -/
theorem PowerBalance.lower_barrier_of_bounds [PhysicalPlasma p] [PowerBalance p sv Paux τE T]
    {Tlo s Pmin τs : ℝ} (hTlo : 0 ≤ Tlo) (hs : s ≤ sv Tlo) (hτs : 0 < τs)
    (hP : ∀ t, 0 ≤ t → T t = Tlo → Pmin ≤ Paux t)
    (hτ : ∀ t, 0 ≤ t → T t = Tlo → τs ≤ τE t)
    (hnum : 0 < p.netHeating (fun _ => s) Pmin τs Tlo) (h0 : Tlo ≤ T 0) :
    ∀ t, 0 ≤ t → Tlo ≤ T t :=
  PowerBalance.lower_barrier h0 fun t ht heq =>
    hnum.trans_le (netHeating_ge hTlo hs (hP t ht heq) hτs (hτ t ht heq))

/-- **No runaway from numeric data.** Suppose `T_hi ≥ 0`, `⟨σv⟩(T_hi) ≤ s`, and at each
crossing time of `T_hi` we have `P_aux ≤ P_max` and `τ_E ≤ τ_hot`. If
`netHeating (const s) P_max τ_hot T_hi < 0`, then `T(t) ≤ T_hi` for all `t ≥ 0`
(under the `PowerBalance` hypotheses). -/
theorem PowerBalance.upper_barrier_of_bounds [PhysicalPlasma p] [PowerBalance p sv Paux τE T]
    {Thi s Pmax τh : ℝ} (hThi : 0 ≤ Thi) (hs : sv Thi ≤ s)
    (hP : ∀ t, 0 ≤ t → T t = Thi → Paux t ≤ Pmax)
    (hτ : ∀ t, 0 ≤ t → T t = Thi → τE t ≤ τh)
    (hnum : p.netHeating (fun _ => s) Pmax τh Thi < 0) (h0 : T 0 ≤ Thi) :
    ∀ t, 0 ≤ t → T t ≤ Thi :=
  PowerBalance.upper_barrier h0 fun t ht heq =>
    (netHeating_le hThi hs (hP t ht heq)
      (PowerBalance.tauE_pos (p := p) (sv := sv) (Paux := Paux) (T := T) t ht)
      (hτ t ht heq)).trans_lt hnum

/-- **Conditional burn yield.** If `T(t) ∈ [T_lo, T_hi] ⊆ [1, 60]` keV for
`t ∈ [0, t_b]`, the fusion energy released over `[0, t_b]` is at least
`P_fus(T_lo) · t_b` (monotonicity of the supplied reactivity on `[1, 60]` keV). -/
theorem PowerBalance.fusion_yield_ge [PhysicalPlasma p] [BoschHaleDT sv]
    [PowerBalance p sv Paux τE T] {Tlo Thi tb : ℝ} (htb : 0 ≤ tb) (h1 : 1 ≤ Tlo)
    (h60 : Thi ≤ 60) (hwin : ∀ t ∈ Set.Icc 0 tb, T t ∈ Set.Icc Tlo Thi) :
    p.fusionPower sv Tlo * tb ≤ ∫ t in (0 : ℝ)..tb, p.fusionPower sv (T t) := by
  have := PhysicalPlasma.n_pos (p := p); have := PhysicalPlasma.V_pos (p := p)
  have hcont : ContinuousOn (fun t => p.fusionPower sv (T t)) (Set.uIcc 0 tb) := by
    rw [Set.uIcc_of_le htb]
    have hT : ContinuousOn T (Set.Icc 0 tb) := fun t ht =>
      (PowerBalance.continuousWithinAt (p := p) (sv := sv) (Paux := Paux) (τE := τE)
        ht.1).mono Set.Icc_subset_Ici_self
    have hsv : ContinuousOn (fun t => sv (T t)) (Set.Icc 0 tb) :=
      BoschHaleDT.continuousOn.comp hT fun t ht => show 0 < T t by
        linarith [(hwin t ht).1]
    unfold fusionPower
    exact (continuousOn_const.mul hsv).mul continuousOn_const
  have hmono := intervalIntegral.integral_mono_on htb
    (intervalIntegrable_const (μ := MeasureTheory.volume))
    (hcont.intervalIntegrable) (f := fun _ => p.fusionPower sv Tlo) (fun t ht => by
      have hw := hwin t ht
      have hle : sv Tlo ≤ sv (T t) :=
        BoschHaleDT.monotoneOn ⟨h1, by linarith [hw.2, hw.1]⟩
        ⟨by linarith [hw.1], by linarith [hw.2]⟩ hw.1
      unfold fusionPower fusionEnergy keV
      gcongr)
  simpa [intervalIntegral.integral_const, mul_comm] using hmono

end Fusion

end PlasmaLean
