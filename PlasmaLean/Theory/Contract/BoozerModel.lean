/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.VacuumBoozerTorus

/-!
# Boozer charts of a physical field, and contract clause C2 for a field (audit item AC-1)

Audit item AC-1 (`notes/audit/2026-10-31-refresh-audit.md`; N-34
`notes/theory/dommaschk-qs-defect.md` §5.1). The model-level condition
`BoozerModelOmnigeneity F c κ` (`Theory/Contract/StellaratorContract`) constrains a supplied
`Kinetic.Boozer.BoozerField F`, and a constant model satisfies it for any candidate. The normative
specification (`notes/formalization/00-model-contracts.md`, C2) asks for a chart whose existence is
proved. This file supplies that chart and restates C2 as a property of the physical field.

Sources: Boozer, Phys. Fluids 24 (1981) 1999; White & Boozer, Phys. Fluids 25 (1982); White,
*The Theory of Toroidally Confined Plasmas*, ch. 3; Helander, Rep. Prog. Phys. 77 (2014) 087001,
§§3–4.

## Why these conditions

The vacuum Boozer guiding-centre equations (`Theory/Kinetic/BoozerGuidingCentre`) are the
Euler–Lagrange equations of `L = q (A + ρ_∥ B) · ẋ − H` with `H = q²ρ²|B|²/(2m) + μ|B|`, written
in coordinates `(ψ, θ, φ)` in which

* `B = ∇ψ × ∇θ + ι(ψ) ∇φ × ∇ψ` (contravariant form; then `A = ψ ∇θ − ψ_p(ψ) ∇φ`, `ψ_p' = ι`),
* `B = G ∇φ` (covariant vacuum Boozer form, `I = K = 0`),
* `|B| = F.B(ψ, θ, φ)`.

These three representations are exactly what the model uses, so they are the minimal faithful
set. In terms of a chart `x : (ψ, θ, φ) ↦ Space` with partial derivatives `e_ψ, e_θ, e_φ` and
Jacobian `J = e_ψ · (e_θ × e_φ)`, the dual basis gives `∇ψ × ∇θ = e_φ/J`, `∇φ × ∇ψ = e_θ/J`, so the
contravariant form is `J B = ι e_θ + e_φ`, and the covariant form is `B·e_ψ = 0`, `B·e_θ = 0`,
`B·e_φ = G`.

## Definitions

* `chartRegion c = {(ψ, θ, φ) | 0 < ψ ≤ c}` (the region of the model-level condition);
* `chartPsi x p`, `chartTheta x p`, `chartPhi x p`: the partial derivatives of `x` (the
  Fréchet derivative applied to the coordinate vectors); `chartJac x p = e_ψ · (e_θ × e_φ)`;
* **`BoozerChart B Ω c F`**: a chart `x`, `C¹` near every point of the region, `2π`-periodic in
  `θ` and `φ`, injective modulo the periods on the region, with image exactly `Ω`, nonzero
  Jacobian, and the contravariant form (`contra`), the covariant vacuum Boozer form (`cov_psi`,
  `cov_theta`, `cov_phi`) and `F.B = |B| ∘ x` (`modB`) on the region;
* **`BoozerModelOf B Ω c F`**: such a chart exists;
* **`OmnigeneityContract B Ω c κ_max`** (clause C2 for the field `B`):
  `∃ F, BoozerModelOf B Ω c F ∧ BoozerModelOmnigeneity F c κ_max`.

By the inverse function theorem a chart is a local `C¹` diffeomorphism near every point of
`0 < ψ < c`; with the injectivity clause it is a bijection of `(0, c] × T²` onto `Ω`. The
smoothness of the global inverse is not derived here.

## What a chart implies (each item stated in terms of `B`)

* (a) invariant tori with rotation number `F.ι ψ`: `BoozerChart.flow` (the image of every line
  `t ↦ (ψ, θ + ι t, φ + t)` is a field line, velocity `J B`); in cylindrical form with the
  geometric toroidal angle this is `Contract.FieldTorus` (`BoozerChart.fieldTorus_of_cyl`);
* (b) flux normalisation: `BoozerChart.toroidalFluxDensity` (`B · (e_ψ × e_θ) = 1`, so the
  toroidal flux through the section `φ = const`, `0 < ψ' < ψ`, is `2πψ`) and
  `BoozerChart.poloidalFluxDensity` (`B · (e_φ × e_ψ) = ι = ψ_p'`);
* (c) `|B| ∘ x = F.B` (`modB`), and `BoozerChart.hasDerivAt_modB_phi`: `F.Bφ` is the physical
  derivative `∂_φ (|B| ∘ x)`;
* (d) Boozer angles: `BoozerChart.hasFDerivAt_potential`: for any local potential `Φ` of `B`
  (`∇Φ = B`), `Φ ∘ x` has chart derivative `(0, 0, G)`, i.e. `φ_B = Φ/G` up to a constant (the
  convention `boozerPhiB` of `Theory/Fields/VacuumBoozerTorus`, where `G = 1`);
* `BoozerChart.G_eq`: `G = J |B|²` (the vacuum Boozer Jacobian `J = G/|B|²`);
  `BoozerChart.field_ne_zero`, `BoozerChart.G_ne_zero`.

## C2 for a field

* (iii) consistency: the bridge theorems apply unchanged.
  `omnigeneityContract_of_exactQS` (chart + exact quasisymmetry of the model ⇒ C2 with
  `κ = 0`), `omnigeneityContract_of_qa` (chart + `|B| ∘ x` independent of the Boozer angle `φ`,
  `ι ≥ ι_min > 0` ⇒ C2 with `κ = 0`), `omnigeneityContract_of_defect_le` (chart + `|∂_φ(|B|∘x)| ≤
  δ`, `|B| ≥ B_min` ⇒ C2 with `κ = 2δ/(B_min ι_min)`), `OmnigeneityContract.model` (C2 ⇒ the
  model-level condition for some model).
* (i) accepted fixture, axisymmetric with an explicit Boozer chart: the vacuum field
  `B = ∇φ` (`RationalStellarator.toroidal`) with the chart `torChart R₀` (`R = R₀ e^{r cos θ}`,
  `z = −r sin θ`, `r = √(2ψ)`, geometric toroidal angle; `G = 1`, `ι = 0`, `|B| = 1/R`):
  `torBoozerChart`, `toroidal_boozerModelOf`, `toroidal_omnigeneityContract` (C2 with `κ = 0`;
  vacuously, since `ι = 0` leaves no trapped bounce in the model), `torChart_fieldTorus` (its
  surfaces are `FieldTorus`es with `ι = 0`).
* (ii) rejected fixtures: `not_boozerModelOf_constField` (a constant Boozer model is not a model
  of a field whose `|B|` varies on `Ω`), `toroidal_not_boozerModelOf_constField` (in particular
  for `∇φ`), `not_omnigeneityContract_zero` (the zero field fails C2 on every nonempty region,
  while the model-level condition holds for the constant model).

**Not covered.** Existence of a Boozer chart for a non-integrable field (none exists on a region
containing islands, N-34 §5.2, so no Dommaschk C2 claim is made); non-vacuum Boozer forms
(`I, K ≠ 0`); smoothness of the inverse chart; the magnetic axis `ψ = 0` (excluded).
-/

open scoped RealInnerProductSpace

public section
noncomputable section

namespace PlasmaLean.Contract

open Real Set Filter Topology Matrix WithLp PlasmaLean.Fields PlasmaLean.Kinetic
  PlasmaLean.Kinetic.Boozer
open PlasmaLean.Design.RationalStellarator (toroidal)

/-! ## Charts -/

/-- The chart region `0 < ψ ≤ c` (all angles). -/
@[expose] def chartRegion (c : ℝ) : Set (ℝ × ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 ≤ c}

/-- `e_ψ = ∂x/∂ψ` (the derivative of `x` at `p` applied to `(1, 0, 0)`). -/
@[expose] def chartPsi (x : ℝ × ℝ × ℝ → Space) (p : ℝ × ℝ × ℝ) : Space := fderiv ℝ x p (1, 0, 0)

/-- `e_θ = ∂x/∂θ`. -/
@[expose] def chartTheta (x : ℝ × ℝ × ℝ → Space) (p : ℝ × ℝ × ℝ) : Space :=
  fderiv ℝ x p (0, 1, 0)

/-- `e_φ = ∂x/∂φ`. -/
@[expose] def chartPhi (x : ℝ × ℝ × ℝ → Space) (p : ℝ × ℝ × ℝ) : Space := fderiv ℝ x p (0, 0, 1)

/-- The chart Jacobian `J = e_ψ · (e_θ × e_φ)` (the determinant of the derivative). -/
@[expose] def chartJac (x : ℝ × ℝ × ℝ → Space) (p : ℝ × ℝ × ℝ) : ℝ :=
  tripleFlux (chartPsi x p) (chartTheta x p) (chartPhi x p)

/-- **Vacuum Boozer chart of the field `B` onto `Ω`, for the Boozer model `F`**, on the region
`0 < ψ ≤ c`: a map `x : (ψ, θ, φ) ↦ Space` that is `C¹` near the region, `2π`-periodic in both
angles, injective modulo the periods on the region and onto `Ω`, with nonzero Jacobian, such that
on the region
* `J B = ι(ψ) e_θ + e_φ` (`B = ∇ψ × ∇θ + ι ∇φ × ∇ψ`: each surface `ψ = const` is invariant with
  straight field lines of slope `F.ι ψ`, and `ψ` is the toroidal flux divided by `2π`);
* `B · e_ψ = 0`, `B · e_θ = 0`, `B · e_φ = F.G` (`B = G ∇φ`: the angles are vacuum Boozer angles);
* `F.B = |B| ∘ x`. -/
structure BoozerChart (B : Space → Space) (Ω : Set Space) (c : ℝ) (F : BoozerField) where
  /-- The chart map `(ψ, θ, φ) ↦ x`. -/
  x : ℝ × ℝ × ℝ → Space
  /-- `x` is `C¹` near every point of the region. -/
  contDiffAt : ∀ p ∈ chartRegion c, ContDiffAt ℝ 1 x p
  /-- `2π`-periodicity in `θ`. -/
  per_θ : ∀ ψ θ φ, x (ψ, θ + 2 * π, φ) = x (ψ, θ, φ)
  /-- `2π`-periodicity in `φ`. -/
  per_φ : ∀ ψ θ φ, x (ψ, θ, φ + 2 * π) = x (ψ, θ, φ)
  /-- Injectivity modulo the periods on the region. -/
  inj : ∀ p ∈ chartRegion c, ∀ p' ∈ chartRegion c, x p = x p' →
    p'.1 = p.1 ∧ (∃ m : ℤ, p'.2.1 = p.2.1 + 2 * π * m) ∧ ∃ n : ℤ, p'.2.2 = p.2.2 + 2 * π * n
  /-- The region is mapped onto `Ω`. -/
  image : x '' chartRegion c = Ω
  /-- The Jacobian does not vanish. -/
  jac_ne : ∀ p ∈ chartRegion c, chartJac x p ≠ 0
  /-- Contravariant form `J B = ι e_θ + e_φ`. -/
  contra : ∀ p ∈ chartRegion c, chartJac x p • B (x p) = F.ι p.1 • chartTheta x p + chartPhi x p
  /-- Covariant vacuum Boozer form, `ψ` component: `B · e_ψ = 0`. -/
  cov_psi : ∀ p ∈ chartRegion c, ⟪B (x p), chartPsi x p⟫ = 0
  /-- Covariant vacuum Boozer form, `θ` component: `B · e_θ = 0` (`I = 0`). -/
  cov_theta : ∀ p ∈ chartRegion c, ⟪B (x p), chartTheta x p⟫ = 0
  /-- Covariant vacuum Boozer form, `φ` component: `B · e_φ = G`. -/
  cov_phi : ∀ p ∈ chartRegion c, ⟪B (x p), chartPhi x p⟫ = F.G
  /-- The model field strength is the physical one: `F.B = |B| ∘ x`. -/
  modB : ∀ p ∈ chartRegion c, F.B p.1 p.2.1 p.2.2 = ‖B (x p)‖

/-- **`F` is a vacuum Boozer model of the field `B` on `Ω`** (region `0 < ψ ≤ c`): a
`BoozerChart` exists. -/
@[expose] def BoozerModelOf (B : Space → Space) (Ω : Set Space) (c : ℝ) (F : BoozerField) :
    Prop :=
  Nonempty (BoozerChart B Ω c F)

/-- **Contract clause C2 for the field `B`** on `Ω`: some vacuum Boozer model `F` of `B` on `Ω`
(region `0 < ψ ≤ c`, `BoozerModelOf`) satisfies the model-level condition
`BoozerModelOmnigeneity F c κ_max` (per-bounce radial displacement `≤ κ_max (H/|q|) τ` for
every species, `μ ≥ 0` and energy; `κ_max = 0` is exact omnigeneity). -/
@[expose] def OmnigeneityContract (B : Space → Space) (Ω : Set Space) (c κmax : ℝ) : Prop :=
  ∃ F : BoozerField, BoozerModelOf B Ω c F ∧ BoozerModelOmnigeneity F c κmax

/-! ## Linear-algebra helpers -/

section Helpers

/-- A linear map on `ℝ³` in terms of its values on the coordinate vectors. -/
theorem clm_apply_triple {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℝ × ℝ × ℝ →L[ℝ] E) (v : ℝ × ℝ × ℝ) :
    L v = v.1 • L (1, 0, 0) + v.2.1 • L (0, 1, 0) + v.2.2 • L (0, 0, 1) := by
  rw [← map_smul, ← map_smul, ← map_smul, ← map_add, ← map_add]
  congr 1
  ext <;> simp

/-- `tripleFlux` is linear in its first argument. -/
theorem tripleFlux_smul_add_left (a : ℝ) (U V b w : Space) :
    tripleFlux (a • U + V) b w = a * tripleFlux U b w + tripleFlux V b w := by
  simp only [tripleFlux, cross_apply, dotProduct, Fin.sum_univ_three, WithLp.ofLp_add,
    WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp
  ring

/-- `tripleFlux 0 a b = 0`. -/
theorem tripleFlux_zero_left (a b : Space) : tripleFlux 0 a b = 0 := by
  simp [tripleFlux]

/-- `tripleFlux` of a scalar multiple in the first argument. -/
theorem tripleFlux_smul_left' (a : ℝ) (U b w : Space) :
    tripleFlux (a • U) b w = a * tripleFlux U b w := by
  have h := tripleFlux_smul_add_left a U 0 b w
  rwa [add_zero, tripleFlux_zero_left, add_zero] at h

/-- Cyclic symmetry of `tripleFlux`. -/
theorem tripleFlux_cycle (u v w : Space) : tripleFlux u v w = tripleFlux v w u :=
  triple_product_permutation _ _ _

/-- `tripleFlux w v w = 0`. -/
theorem tripleFlux_self_right (v w : Space) : tripleFlux w v w = 0 :=
  dot_cross_self _ _

/-- `tripleFlux v v w = 0`. -/
theorem tripleFlux_self_left (v w : Space) : tripleFlux v v w = 0 :=
  dot_self_cross _ _

/-- The `ψ` partial derivative from the derivative along the `ψ`-line. -/
theorem chartPsi_eq {x : ℝ × ℝ × ℝ → Space} {p : ℝ × ℝ × ℝ} {v : Space}
    (hx : DifferentiableAt ℝ x p) (hv : HasDerivAt (fun t => x (t, p.2.1, p.2.2)) v p.1) :
    chartPsi x p = v := by
  have hl : HasDerivAt (fun t : ℝ => ((t, p.2.1, p.2.2) : ℝ × ℝ × ℝ)) ((1 : ℝ), (0 : ℝ), (0 : ℝ))
      p.1 := (hasDerivAt_id _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_const _ _))
  exact (hx.hasFDerivAt.comp_hasDerivAt p.1 hl).unique hv

/-- The `θ` partial derivative from the derivative along the `θ`-line. -/
theorem chartTheta_eq {x : ℝ × ℝ × ℝ → Space} {p : ℝ × ℝ × ℝ} {v : Space}
    (hx : DifferentiableAt ℝ x p) (hv : HasDerivAt (fun t => x (p.1, t, p.2.2)) v p.2.1) :
    chartTheta x p = v := by
  have hl : HasDerivAt (fun t : ℝ => ((p.1, t, p.2.2) : ℝ × ℝ × ℝ)) ((0 : ℝ), (1 : ℝ), (0 : ℝ))
      p.2.1 := (hasDerivAt_const _ _).prodMk ((hasDerivAt_id _).prodMk (hasDerivAt_const _ _))
  exact (hx.hasFDerivAt.comp_hasDerivAt p.2.1 hl).unique hv

/-- The `φ` partial derivative from the derivative along the `φ`-line. -/
theorem chartPhi_eq {x : ℝ × ℝ × ℝ → Space} {p : ℝ × ℝ × ℝ} {v : Space}
    (hx : DifferentiableAt ℝ x p) (hv : HasDerivAt (fun t => x (p.1, p.2.1, t)) v p.2.2) :
    chartPhi x p = v := by
  have hl : HasDerivAt (fun t : ℝ => ((p.1, p.2.1, t) : ℝ × ℝ × ℝ)) ((0 : ℝ), (0 : ℝ), (1 : ℝ))
      p.2.2 := (hasDerivAt_const _ _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_id _))
  exact (hx.hasFDerivAt.comp_hasDerivAt p.2.2 hl).unique hv

/-- Two cylindrical points with the same toroidal direction coincide only if their `R` and `z`
agree. -/
theorem cylPoint_inj {R R' φ φ' z z' : ℝ} (hc : cos φ' = cos φ) (hs : sin φ' = sin φ)
    (h : cylPoint R φ z = cylPoint R' φ' z') : R = R' ∧ z = z' := by
  have h0 := congrArg (fun y : Space => y 0) h
  have h1 := congrArg (fun y : Space => y 1) h
  have h2 := congrArg (fun y : Space => y 2) h
  simp only [cylPoint, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h0 h1 h2
  rw [hc] at h0
  rw [hs] at h1
  refine ⟨?_, h2⟩
  linear_combination cos φ * h0 + sin φ * h1 - (R - R') * sin_sq_add_cos_sq φ

/-- Polar coordinates are injective modulo `2π`. -/
theorem polar_inj {r r' a b : ℝ} (hr : 0 < r) (hr' : 0 < r') (hc : r * cos a = r' * cos b)
    (hs : r * sin a = r' * sin b) : r = r' ∧ ∃ n : ℤ, b = a + 2 * π * n := by
  have h2 : r ^ 2 = r' ^ 2 := by
    linear_combination (r * sin a + r' * sin b) * hs + (r * cos a + r' * cos b) * hc -
      r ^ 2 * sin_sq_add_cos_sq a + r' ^ 2 * sin_sq_add_cos_sq b
  have hrr : r = r' := (pow_left_inj₀ hr.le hr'.le two_ne_zero).1 h2
  subst hrr
  have hca : cos a = cos b := mul_left_cancel₀ hr.ne' hc
  have hsa : sin a = sin b := mul_left_cancel₀ hr.ne' hs
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 (Real.Angle.cos_sin_inj hca hsa)
  exact ⟨rfl, -k, by push_cast; linarith⟩

end Helpers

/-! ## Consequences of a chart -/

namespace BoozerChart

variable {B : Space → Space} {Ω : Set Space} {c : ℝ} {F : BoozerField}

/-- The chart is differentiable at every point of the region. -/
theorem differentiableAt (X : BoozerChart B Ω c F) {p : ℝ × ℝ × ℝ} (hp : p ∈ chartRegion c) :
    DifferentiableAt ℝ X.x p :=
  (X.contDiffAt p hp).differentiableAt one_ne_zero

/-- **(a) Invariant tori with rotation number `F.ι ψ`.** The image of the line
`t ↦ (ψ, θ + t ι, φ + t)` is a field line of `B`: its velocity at `t = 0` is `J B`. -/
theorem flow (X : BoozerChart B Ω c F) {p : ℝ × ℝ × ℝ} (hp : p ∈ chartRegion c) :
    HasDerivAt (fun t => X.x (p.1, p.2.1 + t * F.ι p.1, p.2.2 + t))
      (chartJac X.x p • B (X.x p)) 0 := by
  have hl : HasDerivAt (fun t : ℝ => ((p.1, p.2.1 + t * F.ι p.1, p.2.2 + t) : ℝ × ℝ × ℝ))
      ((0 : ℝ), 1 * F.ι p.1, (1 : ℝ)) 0 :=
    (hasDerivAt_const _ _).prodMk ((((hasDerivAt_id (0 : ℝ)).mul_const _).const_add _).prodMk
      ((hasDerivAt_id (0 : ℝ)).const_add _))
  have h : HasDerivAt (fun t => X.x (p.1, p.2.1 + t * F.ι p.1, p.2.2 + t))
      (fderiv ℝ X.x p ((0 : ℝ), 1 * F.ι p.1, (1 : ℝ))) 0 :=
    (X.differentiableAt hp).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  rw [X.contra p hp]
  convert h using 1
  rw [clm_apply_triple]
  simp [chartTheta, chartPhi]

/-- **(b) Toroidal flux normalisation**: `B · (e_ψ × e_θ) = 1`. Integrated over the section
`φ = const`, `0 < ψ' < ψ`, `θ ∈ [0, 2π]`, the toroidal flux is `2πψ`. -/
theorem toroidalFluxDensity (X : BoozerChart B Ω c F) {p : ℝ × ℝ × ℝ}
    (hp : p ∈ chartRegion c) :
    tripleFlux (B (X.x p)) (chartPsi X.x p) (chartTheta X.x p) = 1 := by
  have h := congrArg (fun v => tripleFlux v (chartPsi X.x p) (chartTheta X.x p)) (X.contra p hp)
  simp only [tripleFlux_smul_left', tripleFlux_smul_add_left, tripleFlux_self_right,
    mul_zero, zero_add] at h
  rw [tripleFlux_cycle (chartPhi X.x p)] at h
  have hJ := X.jac_ne p hp
  rw [chartJac] at hJ h
  exact mul_left_cancel₀ hJ (h.trans (mul_one _).symm)

/-- **(b) Poloidal flux density**: `B · (e_φ × e_ψ) = ι` (`= ψ_p'`). -/
theorem poloidalFluxDensity (X : BoozerChart B Ω c F) {p : ℝ × ℝ × ℝ}
    (hp : p ∈ chartRegion c) :
    tripleFlux (B (X.x p)) (chartPhi X.x p) (chartPsi X.x p) = F.ι p.1 := by
  have h := congrArg (fun v => tripleFlux v (chartPhi X.x p) (chartPsi X.x p)) (X.contra p hp)
  simp only [tripleFlux_smul_left', tripleFlux_smul_add_left, tripleFlux_self_left,
    add_zero] at h
  rw [← tripleFlux_cycle (chartPsi X.x p) (chartTheta X.x p) (chartPhi X.x p)] at h
  have hJ := X.jac_ne p hp
  rw [chartJac] at hJ h
  exact mul_left_cancel₀ hJ (h.trans (mul_comm _ _))

/-- The field does not vanish on the chart image. -/
theorem field_ne_zero (X : BoozerChart B Ω c F) {p : ℝ × ℝ × ℝ} (hp : p ∈ chartRegion c) :
    B (X.x p) ≠ 0 := by
  intro h0
  have h := X.toroidalFluxDensity hp
  rw [h0, tripleFlux_zero_left] at h
  exact zero_ne_one h

/-- **Vacuum Boozer Jacobian**: `G = J |B|²`. -/
theorem G_eq (X : BoozerChart B Ω c F) {p : ℝ × ℝ × ℝ} (hp : p ∈ chartRegion c) :
    F.G = chartJac X.x p * ‖B (X.x p)‖ ^ 2 := by
  have h := congrArg (fun v => ⟪B (X.x p), v⟫) (X.contra p hp)
  simp only [inner_smul_right, inner_add_right, X.cov_theta p hp, X.cov_phi p hp,
    real_inner_self_eq_norm_sq, mul_zero, zero_add] at h
  exact h.symm

/-- `G ≠ 0` for a chart on a nonempty region. -/
theorem G_ne_zero (X : BoozerChart B Ω c F) (hc : 0 < c) : F.G ≠ 0 := by
  have hp : ((c, 0, 0) : ℝ × ℝ × ℝ) ∈ chartRegion c := ⟨hc, le_rfl⟩
  rw [X.G_eq hp]
  exact mul_ne_zero (X.jac_ne _ hp) (pow_ne_zero _ (norm_ne_zero_iff.2 (X.field_ne_zero hp)))

/-- **(c)** Every value of `|B|` on `Ω` is a value of the model field strength. -/
theorem norm_eq_of_mem (X : BoozerChart B Ω c F) {y : Space} (hy : y ∈ Ω) :
    ∃ p ∈ chartRegion c, ‖B y‖ = F.B p.1 p.2.1 p.2.2 := by
  rw [← X.image] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  exact ⟨p, hp, (X.modB p hp).symm⟩

/-- **(c) The model's toroidal derivative is the physical one**: `F.Bφ = ∂_φ (|B| ∘ x)` on the
region (so the quasi-axisymmetry defect of the model is a property of `B`). -/
theorem hasDerivAt_modB_phi (X : BoozerChart B Ω c F) {p : ℝ × ℝ × ℝ}
    (hp : p ∈ chartRegion c) :
    HasDerivAt (fun t => ‖B (X.x (p.1, p.2.1, t))‖) (F.Bφ p.1 p.2.1 p.2.2) p.2.2 := by
  have hl : HasDerivAt (fun t : ℝ => ((p.1, p.2.1, t) : ℝ × ℝ × ℝ)) ((0 : ℝ), (0 : ℝ), (1 : ℝ))
      p.2.2 := (hasDerivAt_const _ _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_id _))
  have h := (F.hasFDerivAt_B p hp.1).comp_hasDerivAt p.2.2 hl
  simp only [gradCLM_apply, mul_zero, mul_one, zero_add] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  exact (X.modB (p.1, p.2.1, t) ⟨hp.1, hp.2⟩).symm

/-- **(d) Boozer angles.** For any local potential `Φ` of `B` at `x(p)` (`∇Φ = B`; in vacuum the
multivalued potential, e.g. `Φ = φ + V` with `B = ∇φ + ∇V`), `Φ ∘ x` has chart derivative
`(0, 0, G)`: `Φ ∘ x = G φ_B + const` locally, the vacuum Boozer-angle convention
(`VacuumBoozer.boozerPhiB`, `G = 1`). -/
theorem hasFDerivAt_potential (X : BoozerChart B Ω c F) {p : ℝ × ℝ × ℝ}
    (hp : p ∈ chartRegion c) {Φ : Space → ℝ}
    (hΦ : HasFDerivAt Φ (innerSL ℝ (B (X.x p))) (X.x p)) :
    HasFDerivAt (fun q => Φ (X.x q)) (gradCLM 0 0 F.G) p := by
  have h : HasFDerivAt (fun q => Φ (X.x q)) ((innerSL ℝ (B (X.x p))).comp (fderiv ℝ X.x p)) p :=
    hΦ.comp p (X.differentiableAt hp).hasFDerivAt
  convert h using 1
  refine ContinuousLinearMap.ext fun v => ?_
  rw [ContinuousLinearMap.comp_apply, clm_apply_triple (fderiv ℝ X.x p)]
  simp only [innerSL_apply_apply, inner_add_right, inner_smul_right, gradCLM_apply]
  rw [show fderiv ℝ X.x p (1, 0, 0) = chartPsi X.x p from rfl,
    show fderiv ℝ X.x p (0, 1, 0) = chartTheta X.x p from rfl,
    show fderiv ℝ X.x p (0, 0, 1) = chartPhi X.x p from rfl, X.cov_psi p hp, X.cov_theta p hp,
    X.cov_phi p hp]
  ring

/-- **(a) in cylindrical form**: if the chart uses the geometric toroidal angle on the surface
`ψ` (`x(ψ, θ, φ) = cylPoint (R θ φ) φ (z θ φ)`, `R, z` continuous, `R > 0`), then the surface is a
`Contract.FieldTorus` of `B` with rotation number `F.ι ψ`. -/
theorem fieldTorus_of_cyl (X : BoozerChart B Ω c F) {ψ : ℝ} (hψ : 0 < ψ) (hψc : ψ ≤ c)
    {R z : ℝ → ℝ → ℝ} (hcyl : ∀ θ φ, X.x (ψ, θ, φ) = cylPoint (R θ φ) φ (z θ φ))
    (hR : Continuous (fun q : ℝ × ℝ => R q.1 q.2)) (hz : Continuous (fun q : ℝ × ℝ => z q.1 q.2))
    (hRpos : ∀ θ φ, 0 < R θ φ) : FieldTorus B R z (F.ι ψ) where
  continuous_R := hR
  continuous_z := hz
  R_pos := hRpos
  per_θ_R θ φ := by
    have h := X.per_θ ψ θ φ
    rw [hcyl, hcyl] at h
    exact (cylPoint_inj rfl rfl h).1
  per_θ_z θ φ := by
    have h := X.per_θ ψ θ φ
    rw [hcyl, hcyl] at h
    exact (cylPoint_inj rfl rfl h).2
  per_φ_R θ φ := by
    have h := X.per_φ ψ θ φ
    rw [hcyl, hcyl] at h
    exact (cylPoint_inj (cos_add_two_pi φ).symm (sin_add_two_pi φ).symm h).1
  per_φ_z θ φ := by
    have h := X.per_φ ψ θ φ
    rw [hcyl, hcyl] at h
    exact (cylPoint_inj (cos_add_two_pi φ).symm (sin_add_two_pi φ).symm h).2
  flow θ φ := by
    refine ⟨chartJac X.x (ψ, θ, φ), ?_⟩
    have h := X.flow (p := (ψ, θ, φ)) ⟨hψ, hψc⟩
    simp only [hcyl] at h
    exact h

/-- Under exact quasi-axisymmetry of the physical field in the chart angles (`|B| ∘ x`
independent of `φ`), the model's toroidal derivative vanishes on the region. -/
theorem Bphi_eq_zero_of_qa (X : BoozerChart B Ω c F)
    (hqa : ∀ p ∈ chartRegion c, ∀ t, ‖B (X.x (p.1, p.2.1, t))‖ = ‖B (X.x p)‖) {p : ℝ × ℝ × ℝ}
    (hp : p ∈ chartRegion c) : F.Bφ p.1 p.2.1 p.2.2 = 0 := by
  have h := X.hasDerivAt_modB_phi hp
  rw [show (fun t => ‖B (X.x (p.1, p.2.1, t))‖) = fun _ => ‖B (X.x p)‖ from
    funext (hqa p hp)] at h
  exact h.unique (hasDerivAt_const _ _)

end BoozerChart

/-! ## Clause C2 for a field: consistency with the model-level theorems -/

section C2Field

variable {B : Space → Space} {Ω : Set Space} {c κmax : ℝ} {F : BoozerField}

/-- C2 for a field gives the model-level condition for some Boozer model of the field. -/
theorem OmnigeneityContract.model (h : OmnigeneityContract B Ω c κmax) :
    ∃ F, BoozerModelOf B Ω c F ∧ BoozerModelOmnigeneity F c κmax :=
  h

/-- **(iii) Consistency: chart + exact quasisymmetry of the model ⇒ C2 with `κ = 0`.** The
bridge theorem `omnigenousOn_of_exactQS` applies unchanged to a Boozer model of the field. -/
theorem omnigeneityContract_of_exactQS (hM : BoozerModelOf B Ω c F) (hc : 0 < c) {N M : ℝ}
    (hQS : ∀ x θ φ, 0 < x → x ≤ c → symmetryDefect F N M x θ φ = 0)
    (hinj : InjOn (fun x => N * x - M * F.ψp x) (Ioc 0 c)) : OmnigeneityContract B Ω c 0 :=
  let ⟨X⟩ := hM
  ⟨F, hM, boozerModelOmnigeneity_zero_iff.2 ⟨hc, omnigenousOn_of_exactQS (X.G_ne_zero hc) hQS hinj⟩⟩

/-- **Exact quasi-axisymmetry of the physical field ⇒ C2 with `κ = 0`**: a Boozer chart in which
`|B| ∘ x` does not depend on the Boozer angle `φ`, with `ι ≥ ι_min > 0` on the region. -/
theorem omnigeneityContract_of_qa (X : BoozerChart B Ω c F) (hc : 0 < c)
    (hqa : ∀ p ∈ chartRegion c, ∀ t, ‖B (X.x (p.1, p.2.1, t))‖ = ‖B (X.x p)‖) {ιmin : ℝ}
    (hι0 : 0 < ιmin) (hι : ∀ x ∈ Ioc 0 c, ιmin ≤ F.ι x) : OmnigeneityContract B Ω c 0 :=
  omnigeneityContract_of_exactQS ⟨X⟩ hc (N := 0) (M := 1)
    (fun x θ φ hx hxc => by
      simp [symmetryDefect, X.Bphi_eq_zero_of_qa hqa (p := (x, θ, φ)) ⟨hx, hxc⟩])
    ((twistOn_qa_of_iota_ge hι).injOn hι0)

/-- **Approximate quasi-axisymmetry of the physical field ⇒ C2**: a Boozer chart with
`|B| ≥ B_min > 0` and `|∂_φ (|B| ∘ x)| ≤ δ` on the region and `ι ≥ ι_min > 0` gives C2 with
`κ_max = 2δ/(B_min ι_min)` (bridge theorem `approxOmnigenousOn_of_defect_le`, unchanged). -/
theorem omnigeneityContract_of_defect_le (X : BoozerChart B Ω c F) (hc : 0 < c)
    {Bmin δ ιmin : ℝ} (hBmin : 0 < Bmin) (hι0 : 0 < ιmin)
    (hBlow : ∀ p ∈ chartRegion c, Bmin ≤ ‖B (X.x p)‖)
    (hδ : ∀ p ∈ chartRegion c, ∀ d,
      HasDerivAt (fun t => ‖B (X.x (p.1, p.2.1, t))‖) d p.2.2 → |d| ≤ δ)
    (hι : ∀ x ∈ Ioc 0 c, ιmin ≤ F.ι x) :
    OmnigeneityContract B Ω c (2 * δ / (Bmin * ιmin)) := by
  have hp0 : ((c, 0, 0) : ℝ × ℝ × ℝ) ∈ chartRegion c := ⟨hc, le_rfl⟩
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ _ hp0 _ (X.hasDerivAt_modB_phi hp0))
  refine ⟨F, ⟨X⟩, hc, by positivity, ?_⟩
  refine approxOmnigenousOn_of_defect_le (N := 0) (M := 1) (X.G_ne_zero hc) hBmin hι0
    (fun x θ φ hx hxc => ?_) (fun x θ φ hx hxc => ?_) (twistOn_qa_of_iota_ge hι)
  · rw [X.modB (x, θ, φ) ⟨hx, hxc⟩]
    exact hBlow _ ⟨hx, hxc⟩
  · simpa [symmetryDefect] using hδ (x, θ, φ) ⟨hx, hxc⟩ _ (X.hasDerivAt_modB_phi ⟨hx, hxc⟩)

/-- **Rejected fixture**: a constant Boozer model is not a Boozer model of a field whose
strength takes two different values on `Ω`. -/
theorem not_boozerModelOf_constField {B₀ ι₀ G : ℝ} {y y' : Space} (hy : y ∈ Ω) (hy' : y' ∈ Ω)
    (hne : ‖B y‖ ≠ ‖B y'‖) : ¬ BoozerModelOf B Ω c (constField B₀ ι₀ G) := by
  rintro ⟨X⟩
  obtain ⟨p, -, hp⟩ := X.norm_eq_of_mem hy
  obtain ⟨p', -, hp'⟩ := X.norm_eq_of_mem hy'
  exact hne (hp.trans hp'.symm)

/-- **Rejected fixture**: the zero field has no Boozer model on a nonempty region. -/
theorem not_boozerModelOf_zero (hΩ : Ω.Nonempty) : ¬ BoozerModelOf (fun _ => 0) Ω c F := by
  rintro ⟨X⟩
  obtain ⟨y, hy⟩ := hΩ
  rw [← X.image] at hy
  obtain ⟨p, hp, -⟩ := hy
  exact X.field_ne_zero hp rfl

/-- **Rejected fixture**: the zero field fails C2 on every nonempty region, for every `κ_max`
(whereas the model-level condition is satisfied by a constant model,
`constField_boozerModelOmnigeneity`). -/
theorem not_omnigeneityContract_zero (hΩ : Ω.Nonempty) :
    ¬ OmnigeneityContract (fun _ => 0) Ω c κmax :=
  fun ⟨_, hM, _⟩ => not_boozerModelOf_zero hΩ hM

end C2Field

/-! ## Accepted fixture: the axisymmetric vacuum field `∇φ` with an explicit Boozer chart

Coordinates: `u = log(R/R₀)` and `z`, in which the toroidal flux element `dR dz/R` is `du dz`;
polar coordinates `u = r cos θ`, `z = −r sin θ` with `ψ = r²/2` (so `dψ dθ = du dz`, the sign
making the chart positively oriented). The geometric toroidal angle is the Boozer angle (`G = 1`),
`ι = 0`, `|B| = 1/R = e^{−r cos θ}/R₀`. -/

section Toroidal

variable {R₀ : ℝ}

/-- The radius `R = R₀ e^{√(2ψ) cos θ}` of the chart. -/
@[expose] def torR (R₀ ψ θ : ℝ) : ℝ := R₀ * exp (√(2 * ψ) * cos θ)

/-- The height `z = −√(2ψ) sin θ` of the chart. -/
@[expose] def torZ (ψ θ : ℝ) : ℝ := -(√(2 * ψ) * sin θ)

/-- The **Boozer chart of `∇φ`**: `(ψ, θ, φ) ↦ cylPoint (torR R₀ ψ θ) φ (torZ ψ θ)`. -/
@[expose] def torChart (R₀ : ℝ) (p : ℝ × ℝ × ℝ) : Space :=
  cylPoint (torR R₀ p.1 p.2.1) p.2.2 (torZ p.1 p.2.1)

/-- The region covered by the chart (a solid torus minus its core circle `R = R₀, z = 0`). -/
@[expose] def torRegion (R₀ c : ℝ) : Set Space := torChart R₀ '' chartRegion c

/-- The model field strength `e^{−√(2ψ) cos θ}/R₀`. -/
@[expose] def torB (R₀ ψ θ : ℝ) : ℝ := exp (-(√(2 * ψ) * cos θ)) / R₀

/-- The chart radius is positive. -/
theorem torR_pos (hR₀ : 0 < R₀) (ψ θ : ℝ) : 0 < torR R₀ ψ θ := by
  unfold torR; positivity

/-- Derivative of the model field strength on `ψ > 0`. -/
theorem torB_hasFDerivAt (R₀ : ℝ) (p : ℝ × ℝ × ℝ) (hp : 0 < p.1) :
    HasFDerivAt (fun p : ℝ × ℝ × ℝ => torB R₀ p.1 p.2.1)
      (gradCLM (-(cos p.2.1 / √(2 * p.1)) * torB R₀ p.1 p.2.1)
        (√(2 * p.1) * sin p.2.1 * torB R₀ p.1 p.2.1) 0) p := by
  have hx : HasFDerivAt (fun p : ℝ × ℝ × ℝ => p.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    hasFDerivAt_fst
  have hy : HasFDerivAt (fun p : ℝ × ℝ × ℝ => p.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    hasFDerivAt_snd.fst
  have h2 : HasFDerivAt (fun y : ℝ × ℝ × ℝ => 2 * y.1)
      ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p := by
    convert hx.const_mul (2 : ℝ) using 1
  have hr := h2.sqrt (show 2 * p.1 ≠ 0 by positivity)
  have hrpos : 0 < √(2 * p.1) := sqrt_pos.mpr (by positivity)
  have he : HasFDerivAt (fun y : ℝ × ℝ × ℝ => exp (-(√(2 * y.1) * cos y.2.1))) _ p :=
    (hr.mul hy.cos).neg.exp
  have hall := HasFDerivAt.mul_const he R₀⁻¹
  convert hall using 1
  · funext y; simp only [torB, div_eq_mul_inv]
  refine ContinuousLinearMap.ext fun v => ?_
  simp [torB, Pi.mul_apply]
  field_simp

/-- The chart is `C¹` near every point with `ψ > 0`. -/
theorem torChart_contDiffAt (R₀ : ℝ) {p : ℝ × ℝ × ℝ} (hp : 0 < p.1) :
    ContDiffAt ℝ 1 (torChart R₀) p := by
  have hs : ContDiffAt ℝ 1 (fun q : ℝ × ℝ × ℝ => √(2 * q.1)) p :=
    (contDiffAt_const.mul contDiffAt_fst).sqrt (by positivity)
  have hθ : ContDiffAt ℝ 1 (fun q : ℝ × ℝ × ℝ => q.2.1) p := contDiffAt_fst.comp p contDiffAt_snd
  have hφ : ContDiffAt ℝ 1 (fun q : ℝ × ℝ × ℝ => q.2.2) p := contDiffAt_snd.comp p contDiffAt_snd
  have hR : ContDiffAt ℝ 1 (fun q : ℝ × ℝ × ℝ => torR R₀ q.1 q.2.1) p :=
    contDiffAt_const.mul (hs.mul hθ.cos).exp
  have hZ : ContDiffAt ℝ 1 (fun q : ℝ × ℝ × ℝ => torZ q.1 q.2.1) p := (hs.mul hθ.sin).neg
  refine (contDiffAt_piLp 2).2 fun i => ?_
  fin_cases i
  · exact hR.mul hφ.cos
  · exact hR.mul hφ.sin
  · exact hZ

/-- `d√(2t)/dt = 1/√(2ψ)` at `ψ > 0`. -/
theorem hasDerivAt_sqrt_two_mul {ψ : ℝ} (hψ : 0 < ψ) :
    HasDerivAt (fun t => √(2 * t)) (1 / √(2 * ψ)) ψ := by
  have h := ((hasDerivAt_id ψ).const_mul 2).sqrt (by simp only [id]; positivity)
  have hr : 0 < √(2 * ψ) := sqrt_pos.mpr (by positivity)
  refine h.congr_deriv ?_
  simp only [id]
  field_simp

/-- The chart's `e_ψ`. -/
theorem torChart_psi {ψ θ φ : ℝ} (hψ : 0 < ψ) :
    chartPsi (torChart R₀) (ψ, θ, φ) = toLp 2 ![torR R₀ ψ θ * (cos θ / √(2 * ψ)) * cos φ,
      torR R₀ ψ θ * (cos θ / √(2 * ψ)) * sin φ, -(sin θ / √(2 * ψ))] := by
  have hs := hasDerivAt_sqrt_two_mul hψ
  have hR : HasDerivAt (fun t => torR R₀ t θ) (torR R₀ ψ θ * (cos θ / √(2 * ψ))) ψ := by
    have h := ((hs.mul_const (cos θ)).exp).const_mul R₀
    refine h.congr_deriv ?_
    simp only [torR]; ring
  have hZ : HasDerivAt (fun t => torZ t θ) (-(sin θ / √(2 * ψ))) ψ := by
    have h := (hs.mul_const (sin θ)).neg
    refine h.congr_deriv ?_
    ring
  exact chartPsi_eq (torChart_contDiffAt R₀ (p := (ψ, θ, φ)) hψ |>.differentiableAt one_ne_zero)
    (hasDerivAt_space3 (hR.mul_const (cos φ)) (hR.mul_const (sin φ)) hZ)

/-- The chart's `e_θ`. -/
theorem torChart_theta {ψ θ φ : ℝ} (hψ : 0 < ψ) :
    chartTheta (torChart R₀) (ψ, θ, φ) = toLp 2 ![torR R₀ ψ θ * -(√(2 * ψ) * sin θ) * cos φ,
      torR R₀ ψ θ * -(√(2 * ψ) * sin θ) * sin φ, -(√(2 * ψ) * cos θ)] := by
  have hR : HasDerivAt (fun t => torR R₀ ψ t) (torR R₀ ψ θ * -(√(2 * ψ) * sin θ)) θ := by
    have h := (((hasDerivAt_cos θ).const_mul (√(2 * ψ))).exp).const_mul R₀
    refine h.congr_deriv ?_
    simp only [torR]; ring
  have hZ : HasDerivAt (fun t => torZ ψ t) (-(√(2 * ψ) * cos θ)) θ :=
    ((hasDerivAt_sin θ).const_mul _).neg
  exact chartTheta_eq (torChart_contDiffAt R₀ (p := (ψ, θ, φ)) hψ |>.differentiableAt one_ne_zero)
    (hasDerivAt_space3 (hR.mul_const (cos φ)) (hR.mul_const (sin φ)) hZ)

/-- The chart's `e_φ`. -/
theorem torChart_phi {ψ θ φ : ℝ} (hψ : 0 < ψ) :
    chartPhi (torChart R₀) (ψ, θ, φ) =
      toLp 2 ![-(torR R₀ ψ θ * sin φ), torR R₀ ψ θ * cos φ, 0] := by
  have h0 : HasDerivAt (fun t => torR R₀ ψ θ * cos t) (torR R₀ ψ θ * -sin φ) φ :=
    (hasDerivAt_cos φ).const_mul _
  have h1 : HasDerivAt (fun t => torR R₀ ψ θ * sin t) (torR R₀ ψ θ * cos φ) φ :=
    (hasDerivAt_sin φ).const_mul _
  have h := hasDerivAt_space3 h0 h1 (hasDerivAt_const φ (torZ ψ θ))
  rw [show torR R₀ ψ θ * -sin φ = -(torR R₀ ψ θ * sin φ) by ring] at h
  exact chartPhi_eq (torChart_contDiffAt R₀ (p := (ψ, θ, φ)) hψ |>.differentiableAt one_ne_zero) h

/-- The chart Jacobian is `R²`. -/
theorem torChart_jac {ψ θ φ : ℝ} (hψ : 0 < ψ) :
    chartJac (torChart R₀) (ψ, θ, φ) = torR R₀ ψ θ ^ 2 := by
  have hr : 0 < √(2 * ψ) := sqrt_pos.mpr (by positivity)
  rw [chartJac, torChart_psi hψ, torChart_theta hψ, torChart_phi hψ]
  simp [tripleFlux, cross_apply, dotProduct, Fin.sum_univ_three]
  field_simp
  linear_combination torR R₀ ψ θ ^ 2 * (sin θ ^ 2 + cos θ ^ 2) * sin_sq_add_cos_sq φ +
    torR R₀ ψ θ ^ 2 * sin_sq_add_cos_sq θ

/-- The **Boozer model of `∇φ`** on `ψ > 0`: `B = e^{−√(2ψ) cos θ}/R₀`, `ι = 0`, `ψ_p = 0`,
`G = 1`. -/
@[expose] def torModel (R₀ : ℝ) : BoozerField where
  B ψ θ _ := torB R₀ ψ θ
  Bψ ψ θ _ := -(cos θ / √(2 * ψ)) * torB R₀ ψ θ
  Bθ ψ θ _ := √(2 * ψ) * sin θ * torB R₀ ψ θ
  Bφ _ _ _ := 0
  ψp _ := 0
  ι _ := 0
  G := 1
  hasFDerivAt_B p hp := torB_hasFDerivAt R₀ p hp
  hasDerivAt_ψp x _ := hasDerivAt_const x 0

/-- `∇φ` at a chart point: `(−sin φ, cos φ, 0)/R`. -/
theorem toroidal_torChart (hR₀ : 0 < R₀) (ψ θ φ : ℝ) :
    toroidal (torChart R₀ (ψ, θ, φ)) =
      toLp 2 ![-sin φ / torR R₀ ψ θ, cos φ / torR R₀ ψ θ, 0] :=
  VacuumBoozer.toroidal_cylPoint (torR_pos hR₀ ψ θ) φ (torZ ψ θ)

/-- Injectivity of the chart modulo the periods, on `ψ > 0`. -/
theorem torChart_inj (hR₀ : 0 < R₀) {p p' : ℝ × ℝ × ℝ} (hp : 0 < p.1) (hp' : 0 < p'.1)
    (h : torChart R₀ p = torChart R₀ p') :
    p'.1 = p.1 ∧ (∃ m : ℤ, p'.2.1 = p.2.1 + 2 * π * m) ∧ ∃ n : ℤ, p'.2.2 = p.2.2 + 2 * π * n := by
  have h0 := congrArg (fun y : Space => y 0) h
  have h1 := congrArg (fun y : Space => y 1) h
  have h2 := congrArg (fun y : Space => y 2) h
  simp only [torChart, cylPoint, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h0 h1 h2
  obtain ⟨hRR, n, hn⟩ := polar_inj (torR_pos hR₀ _ _) (torR_pos hR₀ _ _) h0 h1
  have hu : √(2 * p.1) * cos p.2.1 = √(2 * p'.1) * cos p'.2.1 := by
    simp only [torR] at hRR
    exact exp_injective (mul_left_cancel₀ hR₀.ne' hRR)
  have hv : √(2 * p.1) * sin p.2.1 = √(2 * p'.1) * sin p'.2.1 := by
    simp only [torZ] at h2
    linarith
  obtain ⟨hrr, m, hm⟩ := polar_inj (sqrt_pos.mpr (by positivity)) (sqrt_pos.mpr (by positivity))
    hu hv
  have h2ψ : 2 * p.1 = 2 * p'.1 :=
    (Real.sqrt_inj (by positivity) (by positivity)).1 hrr
  exact ⟨by linarith, ⟨m, hm⟩, ⟨n, hn⟩⟩

/-- **The explicit Boozer chart of `∇φ`** onto `torRegion R₀ c`, for the model `torModel R₀`. -/
def torBoozerChart (hR₀ : 0 < R₀) (c : ℝ) :
    BoozerChart toroidal (torRegion R₀ c) c (torModel R₀) where
  x := torChart R₀
  contDiffAt p hp := torChart_contDiffAt R₀ hp.1
  per_θ ψ θ φ := by simp [torChart, torR, torZ]
  per_φ ψ θ φ := by simp [torChart, cylPoint]
  inj p hp p' hp' h := torChart_inj hR₀ hp.1 hp'.1 h
  image := rfl
  jac_ne p hp := by
    rw [show p = (p.1, p.2.1, p.2.2) from rfl, torChart_jac hp.1]
    exact pow_ne_zero _ (torR_pos hR₀ _ _).ne'
  contra p hp := by
    obtain ⟨ψ, θ, φ⟩ := p
    have hR := (torR_pos hR₀ ψ θ).ne'
    rw [torChart_jac hp.1, torChart_phi hp.1, toroidal_torChart hR₀]
    ext i
    fin_cases i <;> simp [torModel] <;> field_simp
  cov_psi p hp := by
    obtain ⟨ψ, θ, φ⟩ := p
    rw [torChart_psi hp.1, toroidal_torChart hR₀]
    simp [PiLp.inner_apply, Fin.sum_univ_three]
    ring
  cov_theta p hp := by
    obtain ⟨ψ, θ, φ⟩ := p
    rw [torChart_theta hp.1, toroidal_torChart hR₀]
    simp [PiLp.inner_apply, Fin.sum_univ_three]
    ring
  cov_phi p hp := by
    obtain ⟨ψ, θ, φ⟩ := p
    have hR := (torR_pos hR₀ ψ θ).ne'
    rw [torChart_phi hp.1, toroidal_torChart hR₀]
    simp [PiLp.inner_apply, Fin.sum_univ_three, torModel]
    field_simp
    linear_combination sin_sq_add_cos_sq φ
  modB p hp := by
    obtain ⟨ψ, θ, φ⟩ := p
    rw [show torChart R₀ (ψ, θ, φ) = cylPoint (torR R₀ ψ θ) φ (torZ ψ θ) from rfl,
      VacuumBoozer.norm_toroidal_cylPoint (torR_pos hR₀ ψ θ)]
    simp only [torModel, torB, torR, exp_neg]
    rw [mul_inv, div_eq_mul_inv, mul_comm]

/-- **Accepted fixture**: `torModel R₀` is a vacuum Boozer model of `∇φ` on `torRegion R₀ c`. -/
theorem toroidal_boozerModelOf (hR₀ : 0 < R₀) (c : ℝ) :
    BoozerModelOf toroidal (torRegion R₀ c) c (torModel R₀) :=
  ⟨torBoozerChart hR₀ c⟩

/-- The model of `∇φ` is axisymmetric. -/
theorem torModel_axisymmetric : BoozerAxisymmetric (torModel R₀) := fun _ _ _ _ => rfl

/-- **(i) Accepted fixture: the axisymmetric vacuum field `∇φ` satisfies C2 with `κ = 0`** on
`torRegion R₀ c` (with `ι = 0` the model has no trapped bounce, so this holds vacuously; with the
tokamak exclusion it is the consistency check "an axisymmetric current-free field passes C2 and
fails C1"). -/
theorem toroidal_omnigeneityContract (hR₀ : 0 < R₀) {c : ℝ} (hc : 0 < c) :
    OmnigeneityContract toroidal (torRegion R₀ c) c 0 :=
  ⟨torModel R₀, toroidal_boozerModelOf hR₀ c, boozerModelOmnigeneity_zero_iff.2
    ⟨hc, omnigenousOn_of_axisymmetric_iota_zero torModel_axisymmetric fun _ _ => rfl⟩⟩

/-- **(a) for the fixture**: each surface `ψ > 0` of the chart is a `Contract.FieldTorus` of
`∇φ` with rotation number `0`. -/
theorem torChart_fieldTorus (hR₀ : 0 < R₀) {ψ : ℝ} (hψ : 0 < ψ) :
    FieldTorus toroidal (fun θ _ => torR R₀ ψ θ) (fun θ _ => torZ ψ θ) 0 :=
  (torBoozerChart hR₀ ψ).fieldTorus_of_cyl hψ le_rfl (fun _ _ => rfl)
    (by unfold torR; fun_prop) (by unfold torZ; fun_prop) (fun _ _ => torR_pos hR₀ _ _)

/-- **(ii) Rejected fixture**: a constant Boozer model is not a Boozer model of `∇φ` on
`torRegion R₀ c` (`|∇φ| = 1/R` takes the values `e^{∓√(2c)}/R₀` there), although it satisfies
the model-level condition (`constField_boozerModelOmnigeneity`). -/
theorem toroidal_not_boozerModelOf_constField (hR₀ : 0 < R₀) {c : ℝ} (hc : 0 < c)
    {B₀ ι₀ G : ℝ} : ¬ BoozerModelOf toroidal (torRegion R₀ c) c (constField B₀ ι₀ G) := by
  have hm : ∀ θ, ((c, θ, 0) : ℝ × ℝ × ℝ) ∈ chartRegion c := fun _ => ⟨hc, le_rfl⟩
  refine not_boozerModelOf_constField (mem_image_of_mem _ (hm 0)) (mem_image_of_mem _ (hm π)) ?_
  rw [show torChart R₀ (c, 0, 0) = cylPoint (torR R₀ c 0) 0 (torZ c 0) from rfl,
    show torChart R₀ (c, π, 0) = cylPoint (torR R₀ c π) 0 (torZ c π) from rfl,
    VacuumBoozer.norm_toroidal_cylPoint (torR_pos hR₀ c 0),
    VacuumBoozer.norm_toroidal_cylPoint (torR_pos hR₀ c π)]
  intro h
  have h' := mul_left_cancel₀ hR₀.ne' (inv_injective h)
  have hr : 0 < √(2 * c) := sqrt_pos.mpr (by positivity)
  simp only [cos_zero, cos_pi, mul_one, mul_neg] at h'
  have := exp_injective h'
  linarith

end Toroidal

end PlasmaLean.Contract
