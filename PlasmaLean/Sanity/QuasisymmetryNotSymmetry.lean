/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.LieGradient

/-!
# Quasisymmetry is not a PDE symmetry: a local counterexample

The local negative example of `notes/bkm-regularity-and-perelman-burn-bounds.md`, §2.2, and of
the implementation plan, §11.4 (gate E1):

* `B = e_z` (`qsB`), `X = (1 + y) e_x` (`qsX`), `p = y` (`qsP`), on all of `ℝ³` (the note uses
  `0 < y < 1`; nothing here needs the restriction).

The data have zero scalar quasisymmetry error in the sense of the note: both fields are
divergence free, they commute, `X(|B|) = 0`, and `X × B = ∇Φ` with `Φ = -y - y²/2` (`qsPhi`).
The pressure satisfies `X p = 0`. Nevertheless the pressure gradient is not invariant:
`[X, ∇p] = -e_x ≠ 0`. So "zero scalar QS error and `X p = 0`" does not imply that the pressure
force commutes with the generator. The failure is exactly the metric strain term of
`PlasmaLean.Fields.lieBracket_gradient`: `(DX + DXᵀ) ∇p = e_x` (`qs_strain_term`).

This disproves a local operator implication; it is not a toroidal equilibrium.
-/

open scoped RealInnerProductSpace
open InnerProductSpace ContinuousLinearMap VectorField PlasmaLean.Fields

public section
noncomputable section
namespace PlasmaLean.Sanity

/-- The constant magnetic field `B = e_z`. -/
@[expose] def qsB : Space → Space := fun _ => basis 2

/-- The generator `X = (1 + y) e_x`. -/
@[expose] def qsX : Space → Space := fun x => (1 + x 1) • basis 0

/-- The pressure `p = y`. -/
@[expose] def qsP : Space → ℝ := fun x => x 1

/-- The potential `Φ = -y - y²/2` with `X × B = ∇Φ`. -/
@[expose] def qsPhi : Space → ℝ := fun x => -x 1 - x 1 ^ 2 / 2

/-- The coordinate `y` has derivative `EuclideanSpace.proj 1`. -/
theorem hasFDerivAt_coord_one (x : Space) :
    HasFDerivAt (fun y : Space => y 1) (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ) x :=
  (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt

/-- Derivative of the generator: `DX(x) v = v_y e_x`. -/
theorem hasFDerivAt_qsX (x : Space) :
    HasFDerivAt qsX ((EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).smulRight (basis 0)) x :=
  ((hasFDerivAt_coord_one x).const_add 1).smul_const (basis 0)

/-- `DX(x) v = v_y e_x`. -/
theorem fderiv_qsX_apply (x v : Space) : fderiv ℝ qsX x v = v 1 • basis 0 := by
  rw [(hasFDerivAt_qsX x).fderiv]
  rfl

/-- The pressure gradient is `∇p = e_y` everywhere. -/
theorem gradient_qsP : gradient qsP = fun _ => basis 1 := by
  funext x
  have h : fderiv ℝ qsP x = (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ) :=
    (hasFDerivAt_coord_one x).fderiv
  apply space_ext <;> rw [← fderiv_apply_basis, h] <;> simp

/-- `∇Φ = -(1 + y) e_y`. -/
theorem gradient_qsPhi (x : Space) : gradient qsPhi x = (-(1 + x 1)) • basis 1 := by
  have hg : HasDerivAt (fun t : ℝ => -t - t ^ 2 / 2) (-1 - x 1) (x 1) := by
    convert ((hasDerivAt_id' (x 1)).neg.sub ((hasDerivAt_pow 2 (x 1)).div_const 2)) using 1
    norm_num
  have h : fderiv ℝ qsPhi x = (-1 - x 1) • (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ) :=
    (HasDerivAt.comp_hasFDerivAt (f := fun y : Space => y 1) x hg (hasFDerivAt_coord_one x)).fderiv
  apply space_ext <;> rw [← fderiv_apply_basis, h] <;> simp
  ring

/-- `B` is constant: `DB(x) = 0`. -/
theorem fderiv_qsB (x : Space) : fderiv ℝ qsB x = 0 :=
  (hasFDerivAt_const (basis 2) x).fderiv

/-- `B` is divergence free. -/
theorem qsB_divergence (x : Space) : divergence (fderiv ℝ qsB x) = 0 := by
  simp [fderiv_qsB, divergence_apply]

/-- `X` is divergence free. -/
theorem qsX_divergence (x : Space) : divergence (fderiv ℝ qsX x) = 0 := by
  simp [divergence_apply, fderiv_qsX_apply]

/-- `X` and `B` commute: `[X, B] = 0`. -/
theorem qs_lieBracket_X_B (x : Space) : lieBracket ℝ qsX qsB x = 0 := by
  simp [lieBracket, fderiv_qsX_apply, fderiv_qsB, qsB]

/-- `X(|B|) = 0`. -/
theorem qs_X_normB (x : Space) : fderiv ℝ (fun y => ‖qsB y‖) x (qsX x) = 0 := by
  simp [qsB]

/-- `X × B = ∇Φ` with `Φ = -y - y²/2`. -/
theorem qs_cross_eq_gradient (x : Space) : cross (qsX x) (qsB x) = gradient qsPhi x := by
  rw [gradient_qsPhi]
  obtain ⟨h0, h1, h2⟩ := cross_coords (qsX x) (qsB x)
  apply space_ext <;> simp only [h0, h1, h2] <;> simp [qsX, qsB]

/-- **Zero scalar quasisymmetry error.** Both fields are divergence free, they commute,
`X(|B|) = 0`, and `X × B` is a gradient. -/
theorem qs_scalar_error_zero (x : Space) :
    divergence (fderiv ℝ qsB x) = 0 ∧ divergence (fderiv ℝ qsX x) = 0 ∧
      lieBracket ℝ qsX qsB x = 0 ∧ fderiv ℝ (fun y => ‖qsB y‖) x (qsX x) = 0 ∧
      ∃ Φ : Space → ℝ, cross (qsX x) (qsB x) = gradient Φ x :=
  ⟨qsB_divergence x, qsX_divergence x, qs_lieBracket_X_B x, qs_X_normB x,
    qsPhi, qs_cross_eq_gradient x⟩

/-- The pressure is invariant: `X p = ⟪X, ∇p⟫ = 0`. -/
theorem qs_X_pressure (x : Space) : ⟪qsX x, gradient qsP x⟫ = 0 := by
  simp [gradient_qsP, qsX, EuclideanSpace.inner_single_right]

/-- The pressure gradient is not invariant: `[X, ∇p] = -e_x`. -/
theorem qs_lieBracket_X_gradP (x : Space) : lieBracket ℝ qsX (gradient qsP) x = -basis 0 := by
  simp [lieBracket, gradient_qsP, fderiv_qsX_apply]

/-- `[X, ∇p] ≠ 0`. -/
theorem qs_lieBracket_X_gradP_ne_zero (x : Space) : lieBracket ℝ qsX (gradient qsP) x ≠ 0 := by
  rw [qs_lieBracket_X_gradP, neg_ne_zero]
  intro h
  have := congrArg (fun v : Space => v 0) h
  simp at this

/-- **Quasisymmetry is not a PDE symmetry.** There are `B`, `X`, `p` with zero scalar QS error
and `X p = 0` everywhere, but `[X, ∇p] ≠ 0` everywhere. -/
theorem quasisymmetry_not_pde_symmetry :
    ∃ B X : Space → Space, ∃ p : Space → ℝ, ∀ x,
      (divergence (fderiv ℝ B x) = 0 ∧ divergence (fderiv ℝ X x) = 0 ∧
        lieBracket ℝ X B x = 0 ∧ fderiv ℝ (fun y => ‖B y‖) x (X x) = 0 ∧
        ∃ Φ : Space → ℝ, cross (X x) (B x) = gradient Φ x) ∧
      ⟪X x, gradient p x⟫ = 0 ∧ lieBracket ℝ X (gradient p) x ≠ 0 :=
  ⟨qsB, qsX, qsP, fun x =>
    ⟨qs_scalar_error_zero x, qs_X_pressure x, qs_lieBracket_X_gradP_ne_zero x⟩⟩

/-- The obstruction is the metric strain term of `lieBracket_gradient`:
`(DX + DXᵀ) ∇p = e_x`. -/
theorem qs_strain_term (x : Space) :
    (fderiv ℝ qsX x + adjoint (fderiv ℝ qsX x)) (gradient qsP x) = basis 0 := by
  have hp : ContDiffAt ℝ 2 qsP x :=
    ((EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).contDiff).contDiffAt
  have h := lieBracket_gradient_of_contDiffAt (hasFDerivAt_qsX x).differentiableAt hp
  have hXp : (fun y => ⟪qsX y, gradient qsP y⟫) = fun _ => (0 : ℝ) := funext qs_X_pressure
  rw [hXp, gradient_fun_const, qs_lieBracket_X_gradP] at h
  rw [← h]
  simp

end PlasmaLean.Sanity
