/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedResonance

/-!
# Periodicity of the exact-QA reference bounce, and the conditional near-QA drift bound

Companion to `notes/theory/near-qa-trapped-particles.md` (target T4, steps 2–3). Model only:
vacuum Boozer guiding-centre equations for the reactor near-axis family; orbits are supplied.

**Reduced ODE.** In exact QA the right-hand side of the `(ψ, θ, ρ)` equations does not depend on
`φ`; `vred μ` is that autonomous vector field on `ℝ × ℝ × ℝ`, and `wred` the toroidal velocity.
`vred_contDiffAt`: `vred μ` is `C¹` on `ψ > 0`, hence Lipschitz on the compact convex box
`redBox = [ψ_lo, ψ_a] × [−2, 2] × [−1, 1]` (`exists_lipschitz_vred`), which contains every orbit of
the exact-QA start window (`Setup.mem_redBox`).

Results:

* `Setup.periodic`: **a return of the reduced state forces periodicity** (Grönwall uniqueness,
  `periodic_of_return`): if `(ψ, θ, ρ)(P) = (ψ, θ, ρ)(0)` then `(ψ, θ, ρ)(t + kP) = (ψ, θ, ρ)(t)`
  and `φ(t + kP) = φ(t) + k Δ`, `Δ = φ(P) − φ(0)`, as long as `t + kP ≤ T`.
* `exactQA_reference_bounce`: combining with `exactQA_bounce_precession`, every orbit of the
  exact-QA start window is a **periodic reference bounce** with period `P ≤ 1.6 ms` and
  toroidal shift `Δ ∈ [0.7, 2.6]`, `|sin Δ| ≥ 1/2`.
* `reactorQA_trapped_drift_of_reference`: the **conditional near-QA drift bound** (step 3 with
  the remainder as a hypothesis): for a `reactorQA` orbit with turning points `τ k`, if its kicks
  over `[τ k, τ (k+1)]` are within `R` of the reference kicks `∫ g sin 2φ_ref` over the `k`-th
  reference period (with the reference amplitude `g = −(q²ρ²B/m + μ)(2ψ/B₀)(2b₁)`), then
  `|q| ι₀ |ψ(τ N) − ψ(τ 0)| ≤ 4 ∫₀ᴾ |g| + N R`.

**Not proved** (the remaining gap to a trapped-alpha confinement time): a bound on `R`. A single
global reference orbit is too rigid for many bounces (the bounce phase drifts with `ψ₀`: phase
shear), so the remainder must be controlled by re-anchoring the reference every bounce together
with a Grönwall comparison over one bounce; neither is attempted here.
-/
public section
noncomputable section
namespace PlasmaLean.Design.NearAxisQATrappedPeriodic
open PlasmaLean.Kinetic.Boozer PlasmaLean.Design.NearAxisQA
  PlasmaLean.Design.NearAxisQATrappedBounce
  PlasmaLean.Design.NearAxisQATrappedCells PlasmaLean.Design.NearAxisQATrappedResonance Real Set

/-! ## The reduced vector field -/

/-- Field strength `B(ψ, θ)` of exact QA. -/
@[expose] def Bf (x th : ℝ) : ℝ :=
  57 / 10 - 399 / 1000 * √(20 / 57 * x) * cos th +
    20 / 57 * x * (-302 / 10000 + 33 / 1000 * cos th ^ 2)

/-- `∂_ψB` of exact QA. -/
@[expose] def Bψf (x th : ℝ) : ℝ :=
  -(7 / 100 * cos th * (√(20 / 57 * x))⁻¹ + 20 / 57 * (302 / 10000 - 33 / 1000 * cos th ^ 2))

/-- `∂_θB` of exact QA. -/
@[expose] def Bθf (x th : ℝ) : ℝ :=
  sin th * (399 / 1000 * √(20 / 57 * x) - 66 / 1000 * (20 / 57 * x) * cos th)

/-- The autonomous reduced vector field `(ψ̇, θ̇, ρ̇)` of exact QA (magnetic moment `μ`). -/
@[expose] def vred (μ : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (-(mα * μ + qα ^ 2 * p.2.2 ^ 2 * Bf p.1 p.2.1) * Bθf p.1 p.2.1 / (mα * qα),
   (μ / qα + qα * p.2.2 ^ 2 * Bf p.1 p.2.1 / mα) * Bψf p.1 p.2.1 +
      qα * p.2.2 * Bf p.1 p.2.1 ^ 2 * (211 / 500) / (581 / 10 * mα),
   -(mα * μ + qα ^ 2 * p.2.2 ^ 2 * Bf p.1 p.2.1) * (0 + 211 / 500 * Bθf p.1 p.2.1) /
      (581 / 10 * mα * qα))

/-- The toroidal velocity `φ̇ = qρB²/(Gm)` as a function of the reduced state. -/
@[expose] def wred (p : ℝ × ℝ × ℝ) : ℝ := qα * p.2.2 * Bf p.1 p.2.1 ^ 2 / (581 / 10 * mα)

/-- The compact convex box `[ψ_lo, ψ_a] × [−2, 2] × [−1, 1]` in reduced state space. -/
@[expose] def redBox : Set (ℝ × ℝ × ℝ) := Icc psiLo psiEdge ×ˢ (Icc (-2) 2 ×ˢ Icc (-1) 1)

/-- `vred μ` is `C¹` wherever `ψ > 0`. -/
theorem vred_contDiffAt (μ : ℝ) {p : ℝ × ℝ × ℝ} (hp : 0 < p.1) : ContDiffAt ℝ 1 (vred μ) p := by
  have h1 : (20 / 57 * p.1) ≠ 0 := by positivity
  have h2 : √(20 / 57 * p.1) ≠ 0 := by positivity
  unfold vred Bf Bθf Bψf
  fun_prop (disch := assumption)

/-- `vred μ` is Lipschitz on `redBox`. -/
theorem exists_lipschitz_vred (μ : ℝ) : ∃ K, LipschitzOnWith K (vred μ) redBox := by
  apply ContDiffOn.exists_lipschitzOnWith (n := 1) _ one_ne_zero
    ((convex_Icc _ _).prod ((convex_Icc _ _).prod (convex_Icc _ _)))
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  intro p hp
  have : 0 < p.1 := lt_of_lt_of_le (by norm_num [psiLo]) hp.1.1
  exact (vred_contDiffAt μ this).contDiffWithinAt

end PlasmaLean.Design.NearAxisQATrappedPeriodic

/-! ## Orbits of the exact-QA start window solve the reduced ODE -/

namespace PlasmaLean.Design.NearAxisQATrappedResonance.Setup
open PlasmaLean.Kinetic.Boozer PlasmaLean.Design.NearAxisQA
  PlasmaLean.Design.NearAxisQATrappedBounce
  PlasmaLean.Design.NearAxisQATrappedCells PlasmaLean.Design.NearAxisQATrappedPeriodic Real Set
variable {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (S : Setup μ T ψ θ φ ρ)
include S

/-- The reduced state stays in `redBox`. -/
theorem mem_redBox {t : ℝ} (ht : t ∈ Icc 0 T) : (ψ t, θ t, ρ t) ∈ redBox := by
  have hb := S.band ht
  have hθ := S.theta ht
  have hρ := abs_le.mp (hb.2.trans (by norm_num [rhoMax] : rhoMax ≤ 1))
  have hπ := pi_lt_d2
  exact ⟨hb.1, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩, hρ.1, hρ.2⟩

/-- The reduced state solves `ẏ = vred μ y`. -/
theorem hasDerivAt_red {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivAt (fun s => (ψ s, θ s, ρ s)) (vred μ (ψ t, θ t, ρ t)) t := by
  have h := (S.orbit.dψ t ht).prodMk ((S.orbit.dθ t ht).prodMk (S.orbit.dρ t ht))
  convert h using 1
  have eB : along exactQA.B ψ θ φ t = Bf (ψ t) (θ t) := by
    simp only [along]; rw [exactQA_B_eq]; rfl
  have eψ : along exactQA.Bψ ψ θ φ t = Bψf (ψ t) (θ t) := by
    simp only [along]; rw [exactQA_Bψ_eq]; rfl
  have eθ : along exactQA.Bθ ψ θ φ t = Bθf (ψ t) (θ t) := by
    simp only [along]; rw [exactQA_Bθ_eq]; rfl
  have eφ : along exactQA.Bφ ψ θ φ t = 0 := by simp only [along]; exact exactQA_Bφ _ _ _
  rw [eB, eψ, eθ, eφ, show exactQA.ι (ψ t) = 211 / 500 from rfl,
    show exactQA.G = 581 / 10 from rfl]
  rfl

/-- The toroidal angle solves `φ̇ = wred y`. -/
theorem hasDerivAt_phi {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivAt φ (wred (ψ t, θ t, ρ t)) t := by
  have h := S.orbit.dφ t ht
  convert h using 1
  have eB : along exactQA.B ψ θ φ t = Bf (ψ t) (θ t) := by
    simp only [along]; rw [exactQA_B_eq]; rfl
  rw [eB, show exactQA.G = 581 / 10 from rfl]
  rfl

/-- **Periodicity from a return** (ODE uniqueness). If the reduced state returns at `P > 0`, then
`(ψ, θ, ρ)(t + kP) = (ψ, θ, ρ)(t)` and `φ(t + kP) = φ(t) + k (φ(P) − φ(0))` whenever `0 ≤ t` and
`t + kP ≤ T`. -/
theorem periodic {P : ℝ} (hP : 0 < P) (hψ : ψ P = ψ 0) (hθ : θ P = θ 0) (hρ : ρ P = ρ 0) :
    ∀ k : ℕ, ∀ t, 0 ≤ t → t + k * P ≤ T →
      ψ (t + k * P) = ψ t ∧ θ (t + k * P) = θ t ∧ ρ (t + k * P) = ρ t ∧
        φ (t + k * P) = φ t + k * (φ P - φ 0) := by
  obtain ⟨K, hK⟩ := exists_lipschitz_vred μ
  have hret : (fun s => (ψ s, θ s, ρ s)) P = (fun s => (ψ s, θ s, ρ s)) 0 := by
    simp only [hψ, hθ, hρ]
  have hy := periodic_of_return_iter hK (fun t ht => S.hasDerivAt_red ht)
    (fun t ht => S.mem_redBox ht) hP hret
  have hper := periodic_of_return hK (fun t ht => S.hasDerivAt_red ht)
    (fun t ht => S.mem_redBox ht) hP hret
  have hz := shift_of_periodic (w := wred) (z := φ) hP (fun t ht => S.hasDerivAt_phi ht) hper
  intro k t ht htk
  have e := hy k t ht htk
  simp only [Prod.mk.injEq] at e
  exact ⟨e.1, e.2.1, e.2.2, hz k t ht htk⟩

end PlasmaLean.Design.NearAxisQATrappedResonance.Setup

namespace PlasmaLean.Design.NearAxisQATrappedPeriodic
open PlasmaLean.Kinetic.Boozer PlasmaLean.Design.NearAxisQA
  PlasmaLean.Design.NearAxisQATrappedBounce
  PlasmaLean.Design.NearAxisQATrappedCells PlasmaLean.Design.NearAxisQATrappedResonance Real Set

/-- **The exact-QA reference bounce.** Every orbit of the exact-QA start window on `[0, T]`,
`T ≥ 1.6 ms`, is periodic in its reduced state with a period `P ≤ 1.6 ms` and toroidal shift
`Δ = φ(P) − φ(0) ∈ [0.7, 2.6]` per period (so `|sin Δ| ≥ 1/2`):
`(ψ, θ, ρ)(t + kP) = (ψ, θ, ρ)(t)` and `φ(t + kP) = φ(t) + kΔ` while `t + kP ≤ T`. -/
theorem exactQA_reference_bounce {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (S : Setup μ T ψ θ φ ρ)
    (hT : 2 * Lhalf ≤ T) :
    ∃ P : ℝ, 0 < P ∧ P ≤ 2 * Lhalf ∧ φ P - φ 0 ∈ Icc (7 / 10 : ℝ) (13 / 5) ∧
      1 / 2 ≤ |sin (φ P - φ 0)| ∧
      ∀ k : ℕ, ∀ t, 0 ≤ t → t + k * P ≤ T →
        ψ (t + k * P) = ψ t ∧ θ (t + k * P) = θ t ∧ ρ (t + k * P) = ρ t ∧
          φ (t + k * P) = φ t + k * (φ P - φ 0) := by
  obtain ⟨P₁, P, hP₁, hP₁P, hP, -, hρP, -, -, hψ, hθ, hφ⟩ := exactQA_bounce_precession S hT
  have hP0 : 0 < P := hP₁.trans hP₁P
  exact ⟨P, hP0, hP, hφ, abs_sin_ge_half_of_mem hφ,
    S.periodic hP0 hψ hθ (by rw [hρP, S.rho0])⟩

/-! ## The conditional near-QA drift bound -/

/-- The reference kick amplitude along an exact-QA orbit for the symmetry-breaking coefficient
`b₁`: `g = −(q²ρ²B/m + μ) (2ψ/B₀) (2 b₁)`, so that the near-QA kick integrand along the
reference is `g sin 2φ` up to `O(b₁²)` corrections to `B`. -/
@[expose] def refAmp (b₁ μ : ℝ) (ψ θ ρ : ℝ → ℝ) (t : ℝ) : ℝ :=
  -((qα ^ 2 * ρ t ^ 2 * Bf (ψ t) (θ t) / mα + μ) * (2 * ψ t / (57 / 10)) * (2 * b₁))

/-- **Conditional near-QA drift bound for trapped alphas.** Let `ref` be an all-time exact-QA
orbit of the start window (moment `μ`, `Setup` on every `[0, T]`), with period `P` and shift `Δ`
from `exactQA_reference_bounce`. Let `(ψ, θ, φ, ρ)` be a `reactorQA` orbit (moment `μ'`) on
`[0, T]` with turning points `τ 0 ≤ … ≤ τ N ≤ T`. If the actual kicks over `[τ k, τ (k+1)]` are
within `R` of the reference kicks `∫ g sin 2φ_ref` over `[kP, (k+1)P]`, `g = refAmp`, then
`|q| ι₀ |ψ(τ N) − ψ(τ 0)| ≤ 4 ∫₀ᴾ |g| + N R`. The remainder `R` is a hypothesis. -/
theorem reactorQA_trapped_drift_of_reference {μ μ' T : ℝ} {ψr θr φr ρr : ℝ → ℝ}
    (Sref : ∀ T', Setup μ T' ψr θr φr ρr) {ψ θ φ ρ : ℝ → ℝ} {τ : ℕ → ℝ} {N : ℕ} {R : ℝ}
    (h : BoozerGCOrbitOn reactorQA mα qα μ' ψ θ φ ρ T) (hτ : Monotone τ) (h0 : 0 ≤ τ 0)
    (hNT : τ N ≤ T) (hc : ContinuousOn (along reactorQA.Bφ ψ θ φ) (Icc 0 T))
    (hB : ∀ k ≤ N, 0 < along reactorQA.B ψ θ φ (τ k))
    (hv : ∀ k ≤ N, parallelVelocity reactorQA mα qα ψ θ φ ρ (τ k) = 0) :
    ∃ P : ℝ, 0 < P ∧ P ≤ 2 * Lhalf ∧ 1 / 2 ≤ |sin (φr P - φr 0)| ∧
      ((∀ k < N, |(∫ t in τ k..τ (k + 1), qaKick reactorQA mα qα μ' ψ θ φ ρ t) -
          ∫ t in (0 + k * P)..(0 + (k + 1) * P),
            refAmp (-43 / 100000) μ ψr θr ρr t * sin (2 * φr t)| ≤ R) →
        |qα| * (211 / 500) * |ψ (τ N) - ψ (τ 0)| ≤
          4 * (∫ t in (0 : ℝ)..P, |refAmp (-43 / 100000) μ ψr θr ρr t|) + N * R) := by
  obtain ⟨P₁, P, hP₁, hP₁P, hP, -, hρP, -, -, hψP, hθP, hφP⟩ :=
    exactQA_bounce_precession (Sref (2 * Lhalf)) le_rfl
  have hP0 : 0 < P := hP₁.trans hP₁P
  have hsin := abs_sin_ge_half_of_mem hφP
  refine ⟨P, hP0, hP, hsin, fun hclose => ?_⟩
  have hρP' : ρr P = ρr 0 := by rw [hρP, (Sref 0).rho0]
  -- periodicity for every `k` (the reference exists on every horizon)
  have hper : ∀ k : ℕ, ∀ t, 0 ≤ t →
      ψr (t + k * P) = ψr t ∧ θr (t + k * P) = θr t ∧ ρr (t + k * P) = ρr t ∧
        φr (t + k * P) = φr t + k * (φr P - φr 0) := fun k t ht =>
    (Sref (t + k * P)).periodic hP0 hψP hθP hρP' k t ht le_rfl
  -- continuity on one period
  have SP := Sref P
  have hgc : ContinuousOn (refAmp (-43 / 100000) μ ψr θr ρr) (Icc 0 (0 + P)) := by
    rw [zero_add]
    have hB : ContinuousOn (fun t => Bf (ψr t) (θr t)) (Icc 0 P) := by
      unfold Bf
      have hc := continuous_cos.comp_continuousOn SP.cont_theta
      exact (continuousOn_const.sub ((continuousOn_const.mul
        (continuousOn_const.mul SP.cont_psi).sqrt).mul hc)).add
        ((continuousOn_const.mul SP.cont_psi).mul (continuousOn_const.add
          (continuousOn_const.mul (hc.pow 2))))
    unfold refAmp
    exact ((((((continuousOn_const.mul (SP.cont_rho.pow 2)).mul hB).div_const _).add
      continuousOn_const).mul ((continuousOn_const.mul SP.cont_psi).div_const _)).mul
        continuousOn_const).neg
  have hφc : ContinuousOn φr (Icc 0 (0 + P)) := by
    rw [zero_add]; exact fun t ht => (SP.orbit.dφ t ht).continuousAt.continuousWithinAt
  have hΔ : sin (φr P - φr 0) ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hsin; norm_num at hsin
  have key := bounce_drift_of_reference_le (F := reactorQA) (by norm_num [mα]) (by norm_num [qα])
    (by rw [reactorQA_eq, qaField_G]; norm_num) h hτ h0 hNT hc hB hv hP0.le hgc hφc
    (fun k t ht => by
      obtain ⟨e1, e2, e3, -⟩ := hper k t ht.1
      unfold refAmp; rw [e1, e2, e3])
    (fun k t ht => (hper k t ht.1).2.2.2) hΔ hclose
  have hψp : ∀ a b : ℝ, reactorQA.ψp a - reactorQA.ψp b = 211 / 500 * (a - b) := by
    intro a b; simp only [reactorQA_eq, qaField, field]; ring
  rw [hψp, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 211 / 500), zero_add] at key
  have hI : 0 ≤ ∫ t in (0 : ℝ)..P, |refAmp (-43 / 100000) μ ψr θr ρr t| :=
    intervalIntegral.integral_nonneg hP0.le (fun t _ => abs_nonneg _)
  have hs0 : 0 < |sin (φr P - φr 0)| := by linarith
  have : 2 * (∫ t in (0 : ℝ)..P, |refAmp (-43 / 100000) μ ψr θr ρr t|) /
      |sin (φr P - φr 0)| ≤ 4 * ∫ t in (0 : ℝ)..P, |refAmp (-43 / 100000) μ ψr θr ρr t| := by
    rw [div_le_iff₀ hs0]; nlinarith
  calc |qα| * (211 / 500) * |ψ (τ N) - ψ (τ 0)| = |qα| * (211 / 500 * |ψ (τ N) - ψ (τ 0)|) := by
        ring
    _ ≤ _ := key
    _ ≤ _ := by linarith

/-! ## Sanity checks -/

/-- Sanity (degenerate case): at a turning point (`ρ = 0`) the toroidal velocity vanishes. -/
theorem wred_turning (x th : ℝ) : wred (x, th, 0) = 0 := by simp [wred]

/-- Sanity (special case): at a turning point the flux velocity is the pure mirror drift
`ψ̇ = −(μ/q) ∂_θB`. -/
theorem vred_turning_psi (μ x th : ℝ) : (vred μ (x, th, 0)).1 = -(μ / qα) * Bθf x th := by
  simp only [vred]
  have hm : (mα : ℝ) ≠ 0 := by norm_num [mα]
  have hq : (qα : ℝ) ≠ 0 := by norm_num [qα]
  field_simp
  ring

end PlasmaLean.Design.NearAxisQATrappedPeriodic
