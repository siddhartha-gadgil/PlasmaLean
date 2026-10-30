/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Sanity.Transport

/-!
# Strict-audit checks for `Kernel/Transport` (audit of 30 October 2026)

Added by the first strict kernel audit (`notes/audit/2026-10-30-kernel-audit.md`, commit
`cda8bd0`). `Sanity/Transport` already gives degenerate cases (`constField_solution`), concrete
instances (`cosMode_radialHeatTransport`, `linField_radialHeatTransport`, the coefficient
instances) and the divergence-form identity. It had no counterexample to the coefficient laws
or to the solution class. This module adds:

* counterexample to `TransportLaws`: a degenerate coordinate (`D = ψ`) mislabelled `regular` is
  rejected (`mislabelled_not_transportLaws`);
* counterexamples to `ClassicalRadialSolution`: the PDE (`constField_rejects_source`), the
  edge Dirichlet condition (`cosMode_rejects_edge`) and the regular-axis Neumann condition
  (`slopeField_rejects_axis`) each have content;
* zero-duration witness (regression for finding R-1): with `τ = 0` the time derivative is
  taken within the singleton `{0}`, where every value is a derivative, so a time-independent
  profile with a false rate `∂ₜT = −2` is a "classical solution" (`fakeField_zero_duration`),
  although it is a solution on no interval of positive length (`fakeField_not_solution`);
* source domain (regression for finding R-2): the solution class does not keep the temperature
  in the source domain `Tdom` (`solution_outside_Tdom`);
* zero-parameter witness (regression for finding R-3): `D ≡ 0` satisfies the laws (degenerate
  axis kind), and then every steady profile with matching edge data is a solution
  (`noDiffusion_frozen`), so the edge condition is not a parabolic boundary condition there.
-/

public section

noncomputable section

namespace PlasmaLean.Sanity.Audit
open Set Real PlasmaLean.Transport PlasmaLean.Transport.Sanity

/-! ### Counterexample to the coefficient laws -/

/-- Cylinder coefficients `D = ψ` (vanishing at the axis) mislabelled with a `regular` axis. -/
@[expose] def mislabelledCoefficients : RadialCoefficients :=
  .semilinear (fun _ => 1) (fun _ => 0) (fun ψ => ψ) (fun _ => 1) (fun _ _ => 0) univ .regular

/-- **Counterexample.** A coordinate with `D(0,·) = 0` cannot be declared `regular`: the law
`D_axis_regular` rejects it (so the Neumann condition cannot over-determine such a problem). -/
theorem mislabelled_not_transportLaws : ¬ TransportLaws mislabelledCoefficients := fun h =>
  lt_irrefl (0 : ℝ) (h.D_axis_regular rfl 0)

/-! ### Counterexamples to the solution class -/

/-- Unit coefficients with a uniform positive net source `R = 1`. -/
@[expose] def sourceCoefficients : RadialCoefficients :=
  .semilinear (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 0) (fun _ _ => 1) univ .regular

/-- **Counterexample (PDE).** With a uniform source `R = 1` a constant profile is not a solution:
its rate `0` differs from `N[T] = 1`. -/
theorem constField_rejects_source :
    ¬ ClassicalRadialSolution sourceCoefficients (fun _ => 0) 1 (constField 0) := by
  intro h
  have := h.pde 0 ⟨le_rfl, zero_le_one⟩ 0 ⟨le_rfl, zero_le_one⟩
  simp [constField, sourceCoefficients, RadialCoefficients.semilinear_op] at this

/-- **Counterexample (edge condition).** The decaying cosine mode vanishes at the edge, so it is
not a solution with edge data `1`. -/
theorem cosMode_rejects_edge {τ : ℝ} (hτ : 0 ≤ τ) :
    ¬ ClassicalRadialSolution unitCoefficients (fun _ => 1) τ
      (Transport.modeField 0 1 (-(π ^ 2 / 4)) (π / 2)) := by
  intro h
  have := h.edge 0 ⟨le_rfl, hτ⟩
  simp [Transport.modeField] at this

/-- The steady linear profile `T = 1 − ψ` (slope `−1` at the axis). -/
@[expose] def slopeField : RadialField :=
  ⟨fun ψ _ => 1 - ψ, fun _ _ => -1, fun _ _ => 0, fun _ _ => 0⟩

/-- **Counterexample (regular axis).** `T = 1 − ψ` satisfies the PDE and the edge condition for
the unit coefficients, but violates the no-flux condition at the regular axis. -/
theorem slopeField_rejects_axis {τ : ℝ} (hτ : 0 ≤ τ) :
    ¬ ClassicalRadialSolution unitCoefficients (fun _ => 0) τ slopeField := by
  intro h
  have := h.axis rfl 0 ⟨le_rfl, hτ⟩
  norm_num [slopeField] at this

/-! ### Zero-duration witness -/

/-- A time-independent profile `T = 1 − ψ²` carrying the false rate `∂ₜT = −2`. -/
@[expose] def fakeField : RadialField :=
  ⟨fun ψ _ => 1 - ψ ^ 2, fun ψ _ => -2 * ψ, fun _ _ => -2, fun _ _ => -2⟩

/-- Within the singleton `{0}` every value is a derivative. -/
theorem hasDerivWithinAt_Icc_self (f : ℝ → ℝ) (a : ℝ) :
    HasDerivWithinAt f a (Icc 0 0) 0 := by
  rw [Icc_self, hasDerivWithinAt_iff_hasFDerivWithinAt]
  refine HasFDerivWithinAt.of_not_accPt ?_
  rw [accPt_iff_clusterPt, Filter.inf_principal]
  simp [ClusterPt]

/-- **Regression (finding R-1, zero-duration witness).** With horizon `τ = 0`, the profile
`T = 1 − ψ²` with the false rate `−2` is accepted as a classical solution of the unit problem
(zero edge data, regular axis): the class then constrains only the initial profile. -/
theorem fakeField_zero_duration :
    ClassicalRadialSolution unitCoefficients (fun _ => 0) 0 fakeField where
  tau_nonneg := le_rfl
  regular :=
    { cont := by
        apply Continuous.continuousOn
        simp only [fakeField]
        fun_prop
      deriv_ψ := fun _ _ ψ _ => by
        have h := ((hasDerivAt_pow 2 ψ).const_sub 1).hasDerivWithinAt (s := Icc 0 1)
        convert h using 1
        · rfl
        · change -2 * ψ = _
          norm_num
      deriv_ψψ := fun _ _ ψ _ => by
        have h := ((hasDerivAt_id ψ).const_mul (-2)).hasDerivWithinAt (s := Icc 0 1)
        convert h using 1
        · rfl
        · change (-2 : ℝ) = _
          norm_num
      deriv_t := fun ψ _ t ht => by
        obtain rfl : t = 0 := le_antisymm ht.2 ht.1
        exact hasDerivWithinAt_Icc_self _ _ }
  pde := fun ψ _ t _ => by
    simp only [fakeField, unitCoefficients, RadialCoefficients.semilinear_op]
    ring
  axis := fun _ _ _ => by simp [fakeField]
  edge := fun _ _ => by simp [fakeField]

/-- The same profile is a solution on no interval of positive length: its true time derivative
is `0`, not `−2`. -/
theorem fakeField_not_solution {τ : ℝ} (hτ : 0 < τ) :
    ¬ ClassicalRadialSolution unitCoefficients (fun _ => 0) τ fakeField := by
  intro h
  have h1 := h.regular.deriv_t 0 ⟨le_rfl, zero_le_one⟩ 0 ⟨le_rfl, hτ.le⟩
  have h2 : HasDerivWithinAt (fun s => fakeField.T 0 s) 0 (Icc 0 τ) 0 :=
    hasDerivWithinAt_const _ _ _
  have := (uniqueDiffOn_Icc hτ 0 ⟨le_rfl, hτ.le⟩).eq_deriv _ h1 h2
  norm_num [fakeField] at this

/-! ### Source domain -/

/-- Unit coefficients whose source law is posed only for `T > 0` (with `R = 0`). -/
@[expose] def posDomainCoefficients : RadialCoefficients :=
  .semilinear (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 0) (fun _ _ => 0) (Ioi 0) .regular

/-- The positive-domain coefficients satisfy the transport laws. -/
instance : TransportLaws posDomainCoefficients where
  Vp_pos := fun _ _ => one_pos
  Vp_deriv := fun _ _ => hasDerivWithinAt_const _ _ _
  D_deriv := fun _ _ _ => hasDerivWithinAt_const _ _ _
  DT_deriv := fun _ _ T => hasDerivAt_const T _
  D_nonneg := fun _ _ _ => zero_le_one
  D_axis := fun h => nomatch h
  D_axis_regular := fun _ _ => one_pos
  Tdom_open := isOpen_Ioi
  R_cont := continuousOn_const

/-- **Regression (finding R-2, source domain).** The constant profile `T ≡ −1` is a classical
solution although its values lie outside the source domain `T > 0`: the kernel evaluates the
source wherever the solution goes, and `R_cont` says nothing there. -/
theorem solution_outside_Tdom :
    RadialHeatTransport posDomainCoefficients (fun _ => -1) 1 (constField (-1)) ∧
      ∀ ψ t, (constField (-1)).T ψ t ∉ posDomainCoefficients.Tdom := by
  refine ⟨{ toClassicalRadialSolution :=
    constField_solution posDomainCoefficients zero_le_one (fun _ _ => rfl) }, fun _ _ => ?_⟩
  simp [constField, posDomainCoefficients, RadialCoefficients.semilinear]

/-! ### Zero diffusion -/

/-- No diffusion at all: `D ≡ 0`, `R = 0`, degenerate axis. -/
@[expose] def noDiffusionCoefficients : RadialCoefficients :=
  .semilinear (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0) univ .degenerate

/-- The zero-diffusion coefficients satisfy the transport laws. -/
instance : TransportLaws noDiffusionCoefficients where
  Vp_pos := fun _ _ => one_pos
  Vp_deriv := fun _ _ => hasDerivWithinAt_const _ _ _
  D_deriv := fun _ _ _ => hasDerivWithinAt_const _ _ _
  DT_deriv := fun _ _ T => hasDerivAt_const T _
  D_nonneg := fun _ _ _ => le_rfl
  D_axis := fun _ _ => rfl
  D_axis_regular := fun h => nomatch h
  Tdom_open := isOpen_univ
  R_cont := continuousOn_const

/-- The frozen profile `T = ψ` (no time dependence). -/
@[expose] def frozenField : RadialField :=
  ⟨fun ψ _ => ψ, fun _ _ => 1, fun _ _ => 0, fun _ _ => 0⟩

/-- **Regression (finding R-3, zero-parameter witness).** With `D ≡ 0` the laws hold and the
frozen, nonsteady-looking profile `T = ψ` is a solution for every horizon: without diffusion the
equation is the ODE `∂ₜT = R` on each surface and the edge datum is not a boundary condition. -/
theorem noDiffusion_frozen {τ : ℝ} (hτ : 0 ≤ τ) :
    RadialHeatTransport noDiffusionCoefficients (fun _ => 1) τ frozenField where
  tau_nonneg := hτ
  regular :=
    { cont := by
        apply Continuous.continuousOn
        simp only [frozenField]
        fun_prop
      deriv_ψ := fun _ _ ψ _ => (hasDerivAt_id ψ).hasDerivWithinAt
      deriv_ψψ := fun _ _ _ _ => hasDerivWithinAt_const _ _ _
      deriv_t := fun _ _ _ _ => hasDerivWithinAt_const _ _ _ }
  pde := fun ψ _ t _ => by
    simp only [frozenField, noDiffusionCoefficients, RadialCoefficients.semilinear_op]
    ring
  axis := fun h => nomatch h
  edge := fun _ _ => rfl

end PlasmaLean.Sanity.Audit
