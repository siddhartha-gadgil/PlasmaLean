/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormLoopCurrentInterval
public import PlasmaLean.Sanity.FormLoopCurrent

/-!
# Sanity checks for `Theory/Fields/FormLoopCurrentInterval`

* Accepted case, interval hypotheses: the section `R = 3 + cos θ`,
  `z = sin θ + 20 max(0, |θ| - π)` at `φ₀ = 0` coincides with the circular torus section for
  `θ ∈ [-π, π]`, but leaves the bent region `z < x²` at `θ = 2π` (`kink_not_mem`). So the
  theorems of `Theory/Fields/FormLoopCurrent` do not apply to it, while the interval theorems
  give zero circulation, zero loop current and zero period for the hyperbolic vacuum field
  (`hyperbolic_poloidalCirculation_kink`, `hyperbolic_loopCurrent_kink`,
  `hyperbolic_period_kink`).
* Accepted case, periodic data: for the circular torus section, closure is derived from
  periodicity (`hyperbolic_poloidalCirculation_periodic`).
* Hypothesis check: for the non-periodic profile `R = 6 + θ` the poloidal loop lies in the bent
  region for `θ ∈ [-π, π]` but does not close up (`spiral_not_closed`), so closure does not
  follow from the other hypotheses.
* Rejected case, a poloidal loop with non-zero circulation: the field of a straight wire
  through `(3, 0, 0)` parallel to the `y`-axis is a vacuum field off the wire
  (`ringField_vacuum`). The circular torus section at `φ₀ = 0` encircles the wire: its poloidal
  circulation is `2π` (`ring_poloidalCirculation`), the loop current is `2π / μ₀`
  (`ring_loopCurrent`), the de Rham period on the loop class is `2π` (`ring_period`), and the
  complement of the wire is not simply connected (`ringOpens_not_simplyConnected`).
-/

@[expose] public section

namespace PlasmaLean.Sanity.FormLoopCurrentInterval

open PlasmaLean PlasmaLean.Vacuum PlasmaLean.Forms PlasmaLean.Fields PlasmaLean.Sanity
open PlasmaLean.Sanity.FormTopology PlasmaLean.Sanity.FormLoopCurrent PlasmaLean.Contract
open TauCeti TopologicalSpace Topology
open scoped RealInnerProductSpace Manifold

/-! ## Accepted: a section that is good only on `[-π, π]` -/

/-- Height profile `z = sin θ + 20 max(0, |θ| - π)`: equal to `sin θ` on `[-π, π]`, not
differentiable at `θ = ±π`, not periodic. -/
noncomputable def kinkZ (θ _φ : ℝ) : ℝ := Real.sin θ + 20 * max 0 (|θ| - Real.pi)

/-- On `[-π, π]` the kinked section is the circular torus section. -/
theorem kink_poloidalLoop {θ : ℝ} (hθ : θ ∈ Set.Icc (-Real.pi) Real.pi) :
    poloidalLoop torusR kinkZ 0 θ = poloidalLoop torusR torusZ 0 θ := by
  have h : max 0 (|θ| - Real.pi) = 0 := max_eq_left (sub_nonpos.2 (abs_le.2 hθ))
  simp [poloidalLoop, kinkZ, torusZ, h]

/-- The kinked section lies in the bent region for `θ ∈ [-π, π]`. -/
theorem kink_mem : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, poloidalLoop torusR kinkZ 0 θ ∈ bentOpens :=
  fun θ hθ => by
    rw [kink_poloidalLoop hθ]
    exact torus_mem θ

/-- The kinked section leaves the bent region at `θ = 2π`: the membership hypothesis of
`poloidalCirculation_eq_periodHom` fails for it. -/
theorem kink_not_mem : ¬ ∀ θ, poloidalLoop torusR kinkZ 0 θ ∈ bentOpens := by
  intro h
  have h2 := h (2 * Real.pi)
  have habs : |2 * Real.pi| - Real.pi = Real.pi := by
    rw [abs_of_pos (by positivity)]
    ring
  have hmax : max 0 (|2 * Real.pi| - Real.pi) = Real.pi := by
    rw [habs]
    exact max_eq_right Real.pi_pos.le
  have hloop : poloidalLoop torusR kinkZ 0 (2 * Real.pi)
      = WithLp.toLp 2 ![3 + Real.cos (2 * Real.pi), 0, kinkZ (2 * Real.pi) 0] := by
    simp [poloidalLoop, cylPoint, torusR]
  rw [hloop] at h2
  change kinkZ (2 * Real.pi) 0 < (3 + Real.cos (2 * Real.pi)) ^ 2 at h2
  rw [kinkZ, hmax, Real.sin_two_pi, Real.cos_two_pi] at h2
  nlinarith [Real.two_le_pi]

/-- The kinked section is `C¹` on `[-π, π]`. -/
theorem kink_contDiffOn :
    ContDiffOn ℝ 1 (poloidalLoop torusR kinkZ 0) (Set.Icc (-Real.pi) Real.pi) :=
  torus_contDiff.contDiffOn.congr fun _ hθ => kink_poloidalLoop hθ

/-- The kinked section closes up over `[-π, π]`. -/
theorem kink_closed :
    poloidalLoop torusR kinkZ 0 (-Real.pi) = poloidalLoop torusR kinkZ 0 Real.pi := by
  rw [kink_poloidalLoop (Set.left_mem_Icc.2 neg_pi_lt_pi.le),
    kink_poloidalLoop (Set.right_mem_Icc.2 neg_pi_lt_pi.le)]
  exact torus_closed.symm

/-- **Accepted case**: the hyperbolic vacuum field has zero circulation around the kinked
section, by the interval form of the simply connected corollary. -/
theorem hyperbolic_poloidalCirculation_kink :
    poloidalCirculation (fun y => hyperbolicField y) torusR kinkZ 0 = 0 :=
  hyperbolic_vacuum_bent.poloidalCirculation_eq_zero_of_simplyConnected_of_Icc kink_mem
    kink_contDiffOn kink_closed

/-- **Accepted case**: so it carries no net current through the kinked section. -/
theorem hyperbolic_loopCurrent_kink (μ₀ : ℝ) :
    loopCurrent μ₀ (fun y => hyperbolicField y) torusR kinkZ 0 = 0 :=
  hyperbolic_vacuum_bent.loopCurrent_eq_zero_of_simplyConnected_of_Icc μ₀ kink_mem
    kink_contDiffOn kink_closed

/-- **Period check**: the de Rham period of the hyperbolic 1-form on the class of the kinked
section is `0`, by `poloidalCirculation_eq_periodHom_of_Icc`. -/
theorem hyperbolic_period_kink :
    periodHom (onOpens bentOpens fun y => flat (hyperbolicField y))
      (intervalCurve (poloidalLoop torusR kinkZ 0) neg_pi_lt_pi.le kink_mem 0)
      (Additive.ofMul (.of (.mk
        (intervalPath neg_pi_lt_pi.le kink_mem kink_contDiffOn.continuousOn kink_closed))))
      = 0 := by
  rw [← poloidalCirculation_eq_periodHom_of_Icc
    (hyperbolic_vacuum_bent.contDiffOn.of_le (by norm_num)) hyperbolic_vacuum_bent.curl_eq_zero
    kink_mem kink_contDiffOn kink_closed]
  exact hyperbolic_poloidalCirculation_kink

/-! ## Accepted: periodic data -/

/-- The circular torus section is `2π`-periodic. -/
theorem torus_periodic : Function.Periodic (poloidalLoop torusR torusZ 0) (2 * Real.pi) :=
  poloidalLoop_periodic (fun θ => by simp [torusR]) (fun θ => by simp [torusZ])

/-- **Accepted case**: zero circulation around the circular torus section, with closure derived
from periodicity and the other hypotheses only on `[-π, π]`. -/
theorem hyperbolic_poloidalCirculation_periodic :
    poloidalCirculation (fun y => hyperbolicField y) torusR torusZ 0 = 0 :=
  hyperbolic_vacuum_bent.poloidalCirculation_eq_zero_of_periodic torus_periodic
    (fun θ _ => torus_mem θ) torus_contDiff.contDiffOn

/-- **Period check, periodic data**: the period on the class of `poloidalPath`, with membership
for every `θ` and closure derived from periodicity, is `0`. -/
theorem hyperbolic_period_periodic :
    periodHom (onOpens bentOpens fun y => flat (hyperbolicField y))
      (poloidalCurve (poloidalLoop_mem_of_periodic torus_periodic fun θ _ => torus_mem θ) 0)
      (Additive.ofMul (.of (.mk (poloidalPath
        (poloidalLoop_mem_of_periodic torus_periodic fun θ _ => torus_mem θ)
        torus_contDiff.continuous (poloidalLoop_closed_of_periodic torus_periodic).symm))))
      = 0 := by
  rw [← poloidalCirculation_eq_periodHom_of_periodic
    (hyperbolic_vacuum_bent.contDiffOn.of_le (by norm_num)) hyperbolic_vacuum_bent.curl_eq_zero
    torus_periodic (fun θ _ => torus_mem θ) torus_contDiff]
  exact hyperbolic_poloidalCirculation_periodic

/-! ## Hypothesis check: a non-periodic profile does not close up -/

/-- A non-periodic radius profile: `R = 6 + θ`. -/
noncomputable def spiralR (θ _φ : ℝ) : ℝ := 6 + θ

/-- The loop of the non-periodic profile lies in the bent region for `θ ∈ [-π, π]`. -/
theorem spiral_mem :
    ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, poloidalLoop spiralR torusZ 0 θ ∈ bentOpens :=
  fun θ hθ => by
    have hloop : poloidalLoop spiralR torusZ 0 θ
        = WithLp.toLp 2 ![6 + θ, 0, Real.sin θ] := by
      simp [poloidalLoop, cylPoint, spiralR, torusZ]
    rw [hloop]
    change Real.sin θ < (6 + θ) ^ 2
    nlinarith [Real.sin_le_one θ, Real.pi_le_four, hθ.1]

/-- **Closure is a hypothesis**: the loop of the non-periodic profile does not close up. -/
theorem spiral_not_closed :
    poloidalLoop spiralR torusZ 0 (-Real.pi) ≠ poloidalLoop spiralR torusZ 0 Real.pi := by
  intro h
  have h0 := congrArg (fun v : Space => v 0) h
  simp only [poloidalLoop, cylPoint, spiralR, Real.cos_zero, mul_one] at h0
  have h0' : 6 + -Real.pi = 6 + Real.pi := by simpa using h0
  linarith [Real.pi_pos]

/-- The non-periodic profile is not `2π`-periodic in `θ`. -/
theorem spiral_not_periodic : ¬ ∀ θ, spiralR (θ + 2 * Real.pi) 0 = spiralR θ 0 := by
  intro h
  have h0 := h 0
  simp only [spiralR] at h0
  linarith [Real.pi_pos]

/-! ## Rejected: a poloidal loop around a wire -/

/-- Squared distance from the line `x = 3`, `z = 0` (parallel to the `y`-axis). -/
noncomputable def ringR2 (y : Euclid3) : ℝ := (y 0 - 3) ^ 2 + y 2 ^ 2

/-- The linear part `(x, y, z) ↦ (-z, 0, x)` of the numerator of the wire field. -/
noncomputable def ringNum : Euclid3 →L[ℝ] Euclid3 :=
  (EuclideanSpace.proj 0 : Euclid3 →L[ℝ] ℝ).smulRight (coordVec 2) -
    (EuclideanSpace.proj 2 : Euclid3 →L[ℝ] ℝ).smulRight (coordVec 0)

/-- The field of a straight wire through `(3, 0, 0)` parallel to the `y`-axis (up to the factor
`μ₀ I / 2π`): `B = (-z, 0, x - 3) / ((x - 3)² + z²)`. -/
noncomputable def ringField (y : Euclid3) : Euclid3 :=
  (ringR2 y)⁻¹ • (ringNum y - (3 : ℝ) • coordVec 2)

/-- The current-free region: space minus the wire. -/
def ringRegion : Set Euclid3 := {y | 0 < ringR2 y}

/-- Coordinates of the numerator: `(-z, 0, x - 3)`. -/
theorem ringNum_coords (y : Euclid3) :
    (ringNum y - (3 : ℝ) • coordVec 2) 0 = -y 2 ∧ (ringNum y - (3 : ℝ) • coordVec 2) 1 = 0 ∧
      (ringNum y - (3 : ℝ) • coordVec 2) 2 = y 0 - 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [ringNum]

/-- Derivative of the squared distance from the wire. -/
theorem hasFDerivAt_ringR2 (y : Euclid3) :
    HasFDerivAt ringR2 ((2 * (y 0 - 3)) • (EuclideanSpace.proj 0 : Euclid3 →L[ℝ] ℝ) +
      (2 * y 2) • (EuclideanSpace.proj 2 : Euclid3 →L[ℝ] ℝ)) y := by
  have h0 := (((EuclideanSpace.proj 0 : Euclid3 →L[ℝ] ℝ).hasFDerivAt (x := y)).sub_const 3).pow 2
  have h2 := ((EuclideanSpace.proj 2 : Euclid3 →L[ℝ] ℝ).hasFDerivAt (x := y)).pow 2
  exact (h0.add h2).congr_fderiv (by ext v; simp)

/-- Derivative of the wire field off the wire. -/
theorem hasFDerivAt_ringField {y : Euclid3} (hy : ringR2 y ≠ 0) :
    HasFDerivAt ringField ((ringR2 y)⁻¹ • ringNum +
      ((-(ringR2 y ^ 2)⁻¹) • ((2 * (y 0 - 3)) • (EuclideanSpace.proj 0 : Euclid3 →L[ℝ] ℝ) +
        (2 * y 2) • (EuclideanSpace.proj 2 : Euclid3 →L[ℝ] ℝ))).smulRight
          (ringNum y - (3 : ℝ) • coordVec 2)) y :=
  ((hasDerivAt_inv hy).comp_hasFDerivAt y (hasFDerivAt_ringR2 y)).smul
    (ringNum.hasFDerivAt.sub_const _)

/-- The complement of the wire is open. -/
theorem isOpen_ringRegion : IsOpen ringRegion :=
  isOpen_lt continuous_const (by unfold ringR2; fun_prop)

/-- The complement of the wire, as an open region. -/
def ringOpens : Opens Space := ⟨ringRegion, isOpen_ringRegion⟩

/-- **The wire field is a vacuum field** off the wire. -/
theorem ringField_vacuum : VacuumField ringRegion ringField := by
  refine ⟨isOpen_ringRegion, ?_, fun y hy => ?_, fun y hy => ?_⟩
  · intro y hy
    have hy' : ringR2 y ≠ 0 := (show 0 < ringR2 y from hy).ne'
    have hr : ContDiff ℝ 2 ringR2 := by unfold ringR2; fun_prop
    exact ((hr.contDiffAt.inv hy').smul
      (ringNum.contDiff.sub contDiff_const).contDiffAt).contDiffWithinAt
  · have hy' : ringR2 y ≠ 0 := (show 0 < ringR2 y from hy).ne'
    rw [fieldDiv, (hasFDerivAt_ringField hy').fderiv, divOp_apply]
    simp [ringNum]
    ring
  · have hy' : ringR2 y ≠ 0 := (show 0 < ringR2 y from hy).ne'
    rw [fieldCurl, (hasFDerivAt_ringField hy').fderiv]
    ext k
    fin_cases k <;> simp [curlOp, ringNum]
    field_simp
    unfold ringR2 at hy' ⊢
    ring

/-- On the circular torus section the distance from the wire is `1`. -/
theorem ringR2_torus (θ : ℝ) : ringR2 (poloidalLoop torusR torusZ 0 θ) = 1 := by
  rw [torus_poloidalLoop]
  simp [ringR2, Real.cos_sq_add_sin_sq]

/-- The circular torus section lies off the wire. -/
theorem torus_mem_ring (θ : ℝ) : poloidalLoop torusR torusZ 0 θ ∈ ringOpens := by
  change 0 < ringR2 (poloidalLoop torusR torusZ 0 θ)
  rw [ringR2_torus]
  exact one_pos

/-- The velocity of the circular torus section. -/
theorem torus_hasDerivAt (θ : ℝ) :
    HasDerivAt (poloidalLoop torusR torusZ 0)
      (WithLp.toLp 2 ![-Real.sin θ * Real.cos 0, -Real.sin θ * Real.sin 0, Real.cos θ]) θ :=
  hasDerivAt_poloidalLoop ((Real.hasDerivAt_cos θ).const_add 3) (Real.hasDerivAt_sin θ)

/-- The wire field is the unit tangent of the circular torus section. -/
theorem ringField_torus_inner (θ : ℝ) :
    ⟪ringField (poloidalLoop torusR torusZ 0 θ), deriv (poloidalLoop torusR torusZ 0) θ⟫ = 1 := by
  rw [(torus_hasDerivAt θ).deriv, ringField, ringR2_torus, inv_one, one_smul,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_three, ringNum, torus_poloidalLoop]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- **Rejected case, Ampère's law for a poloidal loop**: the poloidal circulation of the wire
field around the circular torus section, which encircles the wire, is `2π`. -/
theorem ring_poloidalCirculation :
    poloidalCirculation ringField torusR torusZ 0 = 2 * Real.pi := by
  simp only [poloidalCirculation, lineIntegral, ringField_torus_inner,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- **Rejected case**: the circulation is not zero. -/
theorem ring_poloidalCirculation_ne_zero :
    poloidalCirculation ringField torusR torusZ 0 ≠ 0 := by
  rw [ring_poloidalCirculation]
  positivity

/-- **Rejected case**: the loop current through the section is `2π / μ₀`. -/
theorem ring_loopCurrent (μ₀ : ℝ) :
    loopCurrent μ₀ ringField torusR torusZ 0 = 2 * Real.pi / μ₀ := by
  rw [loopCurrent, ring_poloidalCirculation]

/-- **Period check, non-zero**: the de Rham period of the wire 1-form on the class of the
circular torus section is `2π`, by `poloidalCirculation_eq_periodHom_of_Icc` with closure from
periodicity. -/
theorem ring_period :
    periodHom (onOpens ringOpens fun y => flat (ringField y))
      (intervalCurve (poloidalLoop torusR torusZ 0) neg_pi_lt_pi.le
        (fun θ _ => torus_mem_ring θ) 0)
      (Additive.ofMul (.of (.mk (intervalPath neg_pi_lt_pi.le (fun θ _ => torus_mem_ring θ)
        torus_contDiff.contDiffOn.continuousOn (poloidalLoop_closed_of_periodic torus_periodic)))))
      = 2 * Real.pi := by
  rw [← poloidalCirculation_eq_periodHom_of_Icc (U := ringOpens)
    (ringField_vacuum.contDiffOn.of_le (by norm_num)) ringField_vacuum.curl_eq_zero
    (fun θ _ => torus_mem_ring θ) torus_contDiff.contDiffOn
    (poloidalLoop_closed_of_periodic torus_periodic)]
  exact ring_poloidalCirculation

/-- **The complement of the wire is not simply connected**: otherwise the interval form of the
corollary would give zero circulation around the section. -/
theorem ringOpens_not_simplyConnected : ¬ SimplyConnectedSpace ringOpens := fun _ =>
  ring_poloidalCirculation_ne_zero
    (VacuumField.poloidalCirculation_eq_zero_of_periodic (U := ringOpens) ringField_vacuum
      torus_periodic (fun θ _ => torus_mem_ring θ) torus_contDiff.contDiffOn)

end PlasmaLean.Sanity.FormLoopCurrentInterval
