/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Contract.StellaratorContract
public import PlasmaLean.Theory.Fields.WeakQuasisymmetry
public import PlasmaLean.Design.RationalStellarator

/-!
# Vacuum Boozer angles on one invariant torus, and the per-torus quasi-axisymmetry defect

Research note `notes/theory/dommaschk-qs-defect.md` (N-34), §1, §2 and module A1 of §6. Sources:
Boozer, Phys. Fluids 24 (1981) 1999 (Boozer coordinates); Helander, Rep. Prog. Phys. 77 (2014)
087001, §§3–4 (quasisymmetry in Boozer angles, `B = G∇φ_B + I∇θ_B + K∇ψ`); the vacuum form
`φ_B = Φ` is N-30 §2. The prototype of the algebra is `Design/DommaschkQSProto` (on demand).

## Setting

A field `B : Space → Space` and a torus `K : ℝ → ℝ → Space`, `(θ, φ) ↦ K θ φ`, with rotation
number `ι`: the field lines on the torus are the images of the lines `t ↦ (θ + t ι, φ + t)`
(`Contract.FieldTorus`, whose cylindrical torus is `cylTorus R z`). Derivatives along the torus:

* `thetaDeriv F θ φ = ∂_θ F` and `lineDeriv ι F θ φ = 𝓛F = (∂_φ + ι ∂_θ) F` (the derivative along
  the line of slope `ι`, as in `FieldTorus.flow`), for vector- or scalar-valued `F`;
* `modB B K = |B| ∘ K`; `boozerA B K = B · ∂_θK`; `boozerJac B ι K = B · 𝓛K` (the Boozer
  Jacobian `J`).

**Vacuum** (`VacuumPotentialOn B V K`): along the torus `B = ∇φ + ∇V` with `∇φ =
RationalStellarator.toroidal` (the multivalued potential `Φ = φ + V`, `V` single-valued, as for
`DommaschkQA2R.field`, `field_split`, `hasFDerivAt_potential`). The **vacuum Boozer angles** are
`φ_B = Φ ∘ K = φ + V ∘ K` (`boozerPhiB`) and `θ_B = θ + ι (φ_B − φ)` (`boozerThetaB`).

## Definitions of the defect

* `boozerDeriv ι a J f_θ f_𝓛 = ((1 + ι a) f_𝓛 − ι J f_θ)/J`: the derivative `∂_{φ_B}` at fixed
  `θ_B`, written with `∂_θ` and `𝓛` (`X = ((1 + ι a)/J) 𝓛 − ι ∂_θ`);
* **`torusQADefect B ι K θ φ`** `= [(1 + ι B·∂_θK) 𝓛(|B|∘K) − ι (B·𝓛K) ∂_θ(|B|∘K)]/(B·𝓛K)`
  (`∂_{φ_B}|B|` on the torus; note §2), and **`TorusQADefectLe B ι K δ`**: `|torusQADefect| ≤ δ`
  everywhere on the torus;
* `boozerPhiVec B ι K = ((1 + ι a)/J) 𝓛K − ι ∂_θK`: the Boozer toroidal direction `e_{φ_B}`
  (torus-intrinsic form).

## Results

* Scalar algebra: `boozerDeriv_phiB` (`X φ_B = 1`), `boozerDeriv_thetaB` (`X θ_B = 0`),
  `boozerDeriv_comp` (chain rule for a function of `(θ_B, φ_B)`), `boozerDeriv_eq_chart` (the
  chart form `(−ι v_φ f_θ + (1 + ι v_θ) f_φ)/J` of the note and of the prototype).
* `∇φ` along a cylindrical torus: `inner_toroidal_of_hasDerivAt` (`∇φ · γ' = φ̇` along any curve
  `γ = cylPoint ρ ϕ ζ`), hence `∇φ · ∂_θK = 0`, `∇φ · 𝓛K = 1`.
* Vacuum angle facts (`hasDerivAt_potential_theta/line`, `hasDerivAt_boozerPhiB_theta/line`,
  `hasDerivAt_boozerThetaB_theta/line`): `∂_θ v = a`, `𝓛v = J − 1` (so **`J = 1 + 𝓛v`**,
  `boozerJac_eq_partials`: `J = 1 + v_φ + ι v_θ`), `∂_θφ_B = a`, `𝓛φ_B = J`, `∂_θθ_B = 1 + ι a`,
  `𝓛θ_B = ι J` (straight field lines); `boozerThetaB_sub`: `θ_B − ι φ_B = θ − ι φ`.
* **The Jacobian identity** `boozerJac_eq_normSq_div` (on a `FieldTorus`, no vacuum needed):
  `J = |B|²/B^φ` with `B^φ = B·∇φ` (`toroidalComp`); `FieldTorus.lineDeriv_eq`
  (`𝓛K = B/B^φ`), `FieldTorus.toroidalComp_ne_zero`, `boozerJac_pos_iff` (`J > 0 ⇔ B^φ > 0`).
* **Boozer direction**: `inner_field_boozerPhiVec` (`B · e_{φ_B} = 1`, i.e. `e_{φ_B}·∇Φ = 1`),
  `boozerPhiVec_eq_field` (`e_{φ_B} = B/|B|² − ι(∂_θK − (B·∂_θK/|B|²) B)` on a `FieldTorus`).
* **Link to weak QS**: `qsError_eq_torusQADefect` (`qsError B ξ = torusQADefect` at torus points
  when `ξ = e_{φ_B}` there and `|B|` is differentiable), `WeakQSDefect.torusQADefectLe` (the
  torus defect is bounded by the `δ₂` component of `WeakQSDefect` on any set containing the
  torus), `qsError_le_of_torusQADefectLe`.
* **Link to the Boozer guiding-centre model**: `symmetryDefect_eq_torusQADefect`: if a
  `Kinetic.Boozer.BoozerField F` represents `|B|` on the surface `ψ = ψ₀ > 0` in the vacuum Boozer
  angles, then `symmetryDefect F 0 1 ψ₀ θ_B φ_B = F.Bφ = torusQADefect` (helicity `(0, 1)` is
  quasi-axisymmetry; this is the hypothesis `hξ` of `approxOmnigenousOn_of_defect_le` restricted to
  one surface).
* **QA characterisation**: `torusQADefect_eq_zero_of_qa` (`|B|∘K = F ∘ θ_B` ⇒ defect `0`) and
  `exists_qa_of_torusQADefect_eq_zero` (defect `≡ 0` ⇒ `|B|∘K = F ∘ θ_B`, given
  differentiability, `1 + ι a ≥ m > 0` and `|ι v_φ| ≤ M`: the mixed chart `(θ, φ) ↦ (θ_B, φ)` is
  then a bijection; abstract 2-D step `exists_comp_of_kernel`).
* **Global invertibility**: `bijective_of_strictMono_bdd` (prototype), `bijective_angleMap` and
  `boozerAngles_bijective`: on a `FieldTorus` of a vacuum field with `J > 0` and `V ∘ K` bounded,
  `(θ, φ) ↦ (θ_B, φ_B)` is a bijection of `ℝ²` (along each field line `φ ↦ φ_B` is strictly
  increasing).

## Sanity triad

* degenerate/normalisation: `boozerDeriv_trivial` (`v = 0`: `X = ∂_φ`), `boozerJac_toroidal`
  (`J = 1`, `a = 0` for `B = ∇φ` on every cylindrical torus), `vacuumPotentialOn_toroidal`
  (`∇φ` is vacuum with `V = 0`), `boozerAngles_zero` (`V = 0`: `(θ_B, φ_B) = (θ, φ)`);
  concrete value `boozerDeriv_concrete`;
* accepted (axisymmetric): `circle_fieldTorus` (the circular torus is a `FieldTorus` of `∇φ` with
  `ι = 0`; generally `circ_fieldTorus` for `B = λ ∇φ`) and `torusQADefect_circle` (its defect
  is `0`); generally exact QA has defect `0`
  (`torusQADefect_eq_zero_of_qa`);
* rejected: the rippled toroidal field `rippleField ε = (1 + ε cos φ) ∇φ` (an invariant torus,
  `ripple_fieldTorus`; not a vacuum field) has `torusQADefect = −ε/ρ ≠ 0` at `φ = π/2`
  (`torusQADefect_ripple`, `torusQADefect_ripple_ne_zero`; `not_torusQADefectLe_ripple`: no
  bound `δ < |ε|/(R₀ + r)` holds); `not_bdd_double` for the bound
  hypothesis of `bijective_of_strictMono_bdd`.

**Not covered:** smoothness of the inverse angle map (inverse function theorem); the weighted
Wirtinger bound and the Boozer spectrum (module A2); `B × e_{φ_B} = ∇ψ` and `div e_{φ_B}` (need a
volume chart, note §2 relation 2).
-/

open scoped RealInnerProductSpace

public section
noncomputable section

namespace PlasmaLean.Fields.VacuumBoozer

open Real Filter Topology WithLp PlasmaLean.Contract
open PlasmaLean.Design.RationalStellarator (toroidal winv r2)

/-! ## Derivatives along the torus and the definitions -/

section Defs
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `∂_θ F` at `(θ, φ)`: the derivative of `t ↦ F t φ` at `θ`. -/
@[expose] def thetaDeriv (F : ℝ → ℝ → E) (θ φ : ℝ) : E := deriv (fun t => F t φ) θ

/-- `𝓛F = (∂_φ + ι ∂_θ) F` at `(θ, φ)`: the derivative of `F` along the line
`t ↦ (θ + t ι, φ + t)` of slope `ι` (the field-line direction of a torus with rotation number
`ι`, as in `Contract.FieldTorus.flow`). -/
@[expose] def lineDeriv (ι : ℝ) (F : ℝ → ℝ → E) (θ φ : ℝ) : E :=
  deriv (fun t => F (θ + t * ι) (φ + t)) 0

end Defs

/-- The cylindrical torus `(θ, φ) ↦ cylPoint (R θ φ) φ (z θ φ)` of `Contract.FieldTorus`. -/
@[expose] def cylTorus (R z : ℝ → ℝ → ℝ) (θ φ : ℝ) : Space := cylPoint (R θ φ) φ (z θ φ)

/-- `|B| ∘ K` as a function of the torus angles. -/
@[expose] def modB (B : Space → Space) (K : ℝ → ℝ → Space) (θ φ : ℝ) : ℝ := ‖B (K θ φ)‖

/-- `a = B · ∂_θK` (in vacuum `a = ∂_θ v`, `v = V ∘ K`). -/
@[expose] def boozerA (B : Space → Space) (K : ℝ → ℝ → Space) (θ φ : ℝ) : ℝ :=
  ⟪B (K θ φ), thetaDeriv K θ φ⟫

/-- The **Boozer Jacobian** `J = B · 𝓛K` (in vacuum `J = 1 + 𝓛v = ∂(θ_B, φ_B)/∂(θ, φ)`, and on an
invariant torus `J = |B|²/B^φ`). -/
@[expose] def boozerJac (B : Space → Space) (ι : ℝ) (K : ℝ → ℝ → Space) (θ φ : ℝ) : ℝ :=
  ⟪B (K θ φ), lineDeriv ι K θ φ⟫

/-- The contravariant toroidal component `B^φ = B · ∇φ` at a point of the torus. -/
@[expose] def toroidalComp (B : Space → Space) (K : ℝ → ℝ → Space) (θ φ : ℝ) : ℝ :=
  ⟪toroidal (K θ φ), B (K θ φ)⟫

/-- The scalar operator `∂_{φ_B}|_{θ_B}` written with `f_θ = ∂_θ f` and `f_𝓛 = 𝓛f`:
`((1 + ι a) f_𝓛 − ι J f_θ)/J`. -/
@[expose] def boozerDeriv (ι a J fθ fL : ℝ) : ℝ := ((1 + ι * a) * fL - ι * J * fθ) / J

/-- **The per-torus quasi-axisymmetry defect** `∂_{φ_B}|B|` (note N-34, §2):
`[(1 + ι B·∂_θK) 𝓛(|B|∘K) − ι (B·𝓛K) ∂_θ(|B|∘K)] / (B·𝓛K)`. It uses only derivatives along the
torus, no flux label and no inverse map. -/
@[expose] def torusQADefect (B : Space → Space) (ι : ℝ) (K : ℝ → ℝ → Space) (θ φ : ℝ) : ℝ :=
  boozerDeriv ι (boozerA B K θ φ) (boozerJac B ι K θ φ) (thetaDeriv (modB B K) θ φ)
    (lineDeriv ι (modB B K) θ φ)

/-- The certified per-torus QA bound: `|∂_{φ_B}|B|| ≤ δ` at every point of the torus. -/
@[expose] def TorusQADefectLe (B : Space → Space) (ι : ℝ) (K : ℝ → ℝ → Space) (δ : ℝ) : Prop :=
  ∀ θ φ, |torusQADefect B ι K θ φ| ≤ δ

/-- The **Boozer toroidal direction** `e_{φ_B} = ((1 + ι a)/J) 𝓛K − ι ∂_θK`, tangent to the torus
(torus-intrinsic form; `boozerPhiVec_eq_field` gives the field form). -/
@[expose] def boozerPhiVec (B : Space → Space) (ι : ℝ) (K : ℝ → ℝ → Space) (θ φ : ℝ) : Space :=
  ((1 + ι * boozerA B K θ φ) / boozerJac B ι K θ φ) • lineDeriv ι K θ φ -
    ι • thetaDeriv K θ φ

/-- The **vacuum Boozer toroidal angle** `φ_B = Φ ∘ K = φ + V ∘ K` (`Φ = φ + V`). -/
@[expose] def boozerPhiB (V : Space → ℝ) (K : ℝ → ℝ → Space) (θ φ : ℝ) : ℝ := φ + V (K θ φ)

/-- The **vacuum Boozer poloidal angle** `θ_B = θ + ι (φ_B − φ)`. -/
@[expose] def boozerThetaB (ι : ℝ) (V : Space → ℝ) (K : ℝ → ℝ → Space) (θ φ : ℝ) : ℝ :=
  θ + ι * (boozerPhiB V K θ φ - φ)

/-- **Vacuum along the torus**: `B = ∇φ + ∇V` at every point of the torus, with `V`
single-valued and differentiable there (`Φ = φ + V` is the multivalued scalar potential). -/
@[expose] def VacuumPotentialOn (B : Space → Space) (V : Space → ℝ) (K : ℝ → ℝ → Space) :
    Prop :=
  ∀ θ φ, HasFDerivAt V (innerSL ℝ (B (K θ φ) - toroidal (K θ φ))) (K θ φ)

/-- The note's form of the defect (definitional). -/
theorem torusQADefect_def' (B : Space → Space) (ι : ℝ) (K : ℝ → ℝ → Space) (θ φ : ℝ) :
    torusQADefect B ι K θ φ =
      ((1 + ι * ⟪B (K θ φ), thetaDeriv K θ φ⟫) * lineDeriv ι (modB B K) θ φ -
        ι * ⟪B (K θ φ), lineDeriv ι K θ φ⟫ * thetaDeriv (modB B K) θ φ) /
        ⟪B (K θ φ), lineDeriv ι K θ φ⟫ := rfl

/-- The field-line label is preserved: `θ_B − ι φ_B = θ − ι φ`. -/
theorem boozerThetaB_sub (ι : ℝ) (V : Space → ℝ) (K : ℝ → ℝ → Space) (θ φ : ℝ) :
    boozerThetaB ι V K θ φ - ι * boozerPhiB V K θ φ = θ - ι * φ := by
  unfold boozerThetaB; ring

/-! ## Scalar algebra of `∂_{φ_B}` -/

/-- `X φ_B = 1`: `∂_θ φ_B = a`, `𝓛 φ_B = J`. -/
theorem boozerDeriv_phiB {ι a J : ℝ} (hJ : J ≠ 0) : boozerDeriv ι a J a J = 1 := by
  unfold boozerDeriv; field_simp; ring

/-- `X θ_B = 0`: `∂_θ θ_B = 1 + ι a`, `𝓛 θ_B = ι J`. -/
theorem boozerDeriv_thetaB (ι a J : ℝ) : boozerDeriv ι a J (1 + ι * a) (ι * J) = 0 := by
  unfold boozerDeriv; ring_nf

/-- **Chain rule**: for `f = G(θ_B, φ_B)` with partials `G_θ`, `G_φ`, `X f = G_φ`. -/
theorem boozerDeriv_comp {ι a J Gθ Gφ : ℝ} (hJ : J ≠ 0) :
    boozerDeriv ι a J (Gθ * (1 + ι * a) + Gφ * a) (Gθ * (ι * J) + Gφ * J) = Gφ := by
  unfold boozerDeriv; field_simp; ring

/-- Exact QA (`f = F ∘ θ_B`) has `X f = 0`. -/
theorem boozerDeriv_qa (ι a J F' : ℝ) :
    boozerDeriv ι a J (F' * (1 + ι * a)) (F' * (ι * J)) = 0 := by
  unfold boozerDeriv; ring_nf

/-- The chart form of the note and of the prototype: with `f_𝓛 = f_φ + ι f_θ` and
`v_φ = J − 1 − ι a`, `X f = (−ι v_φ f_θ + (1 + ι a) f_φ)/J`. -/
theorem boozerDeriv_eq_chart (ι a J fθ fφ : ℝ) :
    boozerDeriv ι a J fθ (fφ + ι * fθ) =
      (-(ι * (J - 1 - ι * a)) * fθ + (1 + ι * a) * fφ) / J := by
  unfold boozerDeriv; ring_nf

/-- Degenerate case `v = 0` (`a = 0`, `J = 1`): `X f = f_𝓛 − ι f_θ = f_φ`, i.e. `X = ∂_φ`. -/
theorem boozerDeriv_trivial (ι fθ fL : ℝ) : boozerDeriv ι 0 1 fθ fL = fL - ι * fθ := by
  unfold boozerDeriv; ring

/-- Concrete instance: `ι = −1/4`, `a = 1/10`, `J = 41/40`, `f_θ = 1`, `f_𝓛 = 0`: `X f = 1/4`. -/
theorem boozerDeriv_concrete : boozerDeriv (-1/4) (1/10) (41/40) 1 0 = 1/4 := by
  norm_num [boozerDeriv]

/-! ## `∇φ` along a cylindrical curve -/

/-- `∇φ · γ' = φ̇`: along a curve `γ t = cylPoint (ρ t) (ϕ t) (ζ t)` with `ρ > 0`, the toroidal
field `∇φ = RationalStellarator.toroidal` pairs with the velocity to the rate of the toroidal
angle (no differentiability of `ρ`, `ζ` is needed beyond that of `γ`). -/
theorem inner_toroidal_of_hasDerivAt {ρ ϕ ζ : ℝ → ℝ} {w : Space} {k t₀ : ℝ}
    (hγ : HasDerivAt (fun t => cylPoint (ρ t) (ϕ t) (ζ t)) w t₀) (hϕ : HasDerivAt ϕ k t₀)
    (hρ : 0 < ρ t₀) :
    ⟪toroidal (cylPoint (ρ t₀) (ϕ t₀) (ζ t₀)), w⟫ = k := by
  have h0 := hasDerivAt_coord hγ 0
  have h1 := hasDerivAt_coord hγ 1
  simp only [cylPoint, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  -- `cos ϕ · γ₁ − sin ϕ · γ₀ ≡ 0`
  have hc : HasDerivAt
      (fun t => cos (ϕ t) * (ρ t * sin (ϕ t)) - sin (ϕ t) * (ρ t * cos (ϕ t))) _ t₀ :=
    (hϕ.cos.mul h1).sub (hϕ.sin.mul h0)
  have hzero : (fun t => cos (ϕ t) * (ρ t * sin (ϕ t)) - sin (ϕ t) * (ρ t * cos (ϕ t))) =
      fun _ => (0 : ℝ) := by funext t; ring
  rw [hzero] at hc
  have hu := hc.unique (hasDerivAt_const t₀ (0 : ℝ))
  have hcs := sin_sq_add_cos_sq (ϕ t₀)
  have hr2 : r2 (cylPoint (ρ t₀) (ϕ t₀) (ζ t₀)) = ρ t₀ ^ 2 := by
    simp only [r2, cylPoint, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination ρ t₀ ^ 2 * hcs
  simp only [toroidal, EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_three, dotProduct,
    winv, hr2]
  simp only [cylPoint, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, star_trivial, mul_zero, add_zero]
  have key : cos (ϕ t₀) * w 1 - sin (ϕ t₀) * w 0 = k * ρ t₀ := by
    linear_combination hu + k * ρ t₀ * hcs
  rw [show w 0 * (-(ρ t₀ * sin (ϕ t₀)) * (ρ t₀ ^ 2)⁻¹) + w 1 * (ρ t₀ * cos (ϕ t₀) * (ρ t₀ ^ 2)⁻¹)
      = ρ t₀ * (cos (ϕ t₀) * w 1 - sin (ϕ t₀) * w 0) / ρ t₀ ^ 2 by ring, key]
  field_simp

/-! ## The vacuum Boozer angles on a cylindrical torus -/

section Cyl
variable {B : Space → Space} {V : Space → ℝ} {R z : ℝ → ℝ → ℝ} {ι θ φ : ℝ}

/-- `∇φ · ∂_θK = 0` on a cylindrical torus (a curve of constant toroidal angle). -/
theorem inner_toroidal_theta {w : Space} (hw : HasDerivAt (fun t => cylTorus R z t φ) w θ)
    (hR : 0 < R θ φ) : ⟪toroidal (cylTorus R z θ φ), w⟫ = 0 :=
  inner_toroidal_of_hasDerivAt (ρ := fun t => R t φ) (ϕ := fun _ => φ) (ζ := fun t => z t φ) hw
    (hasDerivAt_const θ φ) hR

/-- `∇φ · 𝓛K = 1` on a cylindrical torus (the toroidal angle advances at unit rate along the
lines `t ↦ (θ + t ι, φ + t)`). -/
theorem inner_toroidal_line {w : Space}
    (hw : HasDerivAt (fun t => cylTorus R z (θ + t * ι) (φ + t)) w 0) (hR : 0 < R θ φ) :
    ⟪toroidal (cylTorus R z θ φ), w⟫ = 1 := by
  have h := inner_toroidal_of_hasDerivAt (ρ := fun t => R (θ + t * ι) (φ + t))
    (ϕ := fun t => φ + t) (ζ := fun t => z (θ + t * ι) (φ + t)) hw
    ((hasDerivAt_id (0 : ℝ)).const_add φ) (by simpa using hR)
  simpa [cylTorus] using h

/-- Along the line through `(θ, φ)` the curve passes through `K θ φ` at `t = 0`. -/
theorem line_zero (F : ℝ → ℝ → Space) : F (θ + 0 * ι) (φ + 0) = F θ φ := by simp

/-- **`∂_θ v = B · ∂_θK`** in vacuum (`v = V ∘ K`; `∇φ · ∂_θK = 0`). -/
theorem hasDerivAt_potential_theta (hV : VacuumPotentialOn B V (cylTorus R z)) {w : Space}
    (hw : HasDerivAt (fun t => cylTorus R z t φ) w θ) (hR : 0 < R θ φ) :
    HasDerivAt (fun t => V (cylTorus R z t φ)) ⟪B (cylTorus R z θ φ), w⟫ θ := by
  have h := (hV θ φ).comp_hasDerivAt θ hw
  rw [innerSL_apply_apply, inner_sub_left, inner_toroidal_theta hw hR, sub_zero] at h
  exact h

/-- **`𝓛v = B · 𝓛K − 1`** in vacuum (`∇φ · 𝓛K = 1`). -/
theorem hasDerivAt_potential_line (hV : VacuumPotentialOn B V (cylTorus R z)) {w : Space}
    (hw : HasDerivAt (fun t => cylTorus R z (θ + t * ι) (φ + t)) w 0) (hR : 0 < R θ φ) :
    HasDerivAt (fun t => V (cylTorus R z (θ + t * ι) (φ + t)))
      (⟪B (cylTorus R z θ φ), w⟫ - 1) 0 := by
  have h := (hV θ φ).comp_hasDerivAt_of_eq 0 hw (line_zero (cylTorus R z)).symm
  rw [innerSL_apply_apply, inner_sub_left, inner_toroidal_line hw hR] at h
  exact h

/-- `∂_θ φ_B = a` (vacuum). -/
theorem hasDerivAt_boozerPhiB_theta (hV : VacuumPotentialOn B V (cylTorus R z))
    (hθ : DifferentiableAt ℝ (fun t => cylTorus R z t φ) θ) (hR : 0 < R θ φ) :
    HasDerivAt (fun t => boozerPhiB V (cylTorus R z) t φ) (boozerA B (cylTorus R z) θ φ) θ := by
  have h := (hasDerivAt_potential_theta hV hθ.hasDerivAt hR).const_add φ
  simpa [boozerPhiB, boozerA, thetaDeriv] using h

/-- `𝓛 φ_B = J` (vacuum): **the Boozer Jacobian is `J = 1 + 𝓛v`**. -/
theorem hasDerivAt_boozerPhiB_line (hV : VacuumPotentialOn B V (cylTorus R z))
    (hL : DifferentiableAt ℝ (fun t => cylTorus R z (θ + t * ι) (φ + t)) 0) (hR : 0 < R θ φ) :
    HasDerivAt (fun t => boozerPhiB V (cylTorus R z) (θ + t * ι) (φ + t))
      (boozerJac B ι (cylTorus R z) θ φ) 0 := by
  have h : HasDerivAt (fun t => (φ + t) + V (cylTorus R z (θ + t * ι) (φ + t)))
      (1 + (⟪B (cylTorus R z θ φ), lineDeriv ι (cylTorus R z) θ φ⟫ - 1)) 0 :=
    ((hasDerivAt_id' (0 : ℝ)).const_add φ).add (hasDerivAt_potential_line hV hL.hasDerivAt hR)
  exact h.congr_deriv (by simp [boozerJac])

/-- `∂_θ θ_B = 1 + ι a` (vacuum). -/
theorem hasDerivAt_boozerThetaB_theta (hV : VacuumPotentialOn B V (cylTorus R z))
    (hθ : DifferentiableAt ℝ (fun t => cylTorus R z t φ) θ) (hR : 0 < R θ φ) :
    HasDerivAt (fun t => boozerThetaB ι V (cylTorus R z) t φ)
      (1 + ι * boozerA B (cylTorus R z) θ φ) θ := by
  have h := (hasDerivAt_id θ).add ((hasDerivAt_potential_theta hV hθ.hasDerivAt hR).const_mul ι)
  convert h using 1
  · funext t; simp [boozerThetaB, boozerPhiB]
  · simp [boozerA, thetaDeriv]

/-- **Straight field lines**: `𝓛 θ_B = ι J = ι 𝓛 φ_B` (vacuum). -/
theorem hasDerivAt_boozerThetaB_line (hV : VacuumPotentialOn B V (cylTorus R z))
    (hL : DifferentiableAt ℝ (fun t => cylTorus R z (θ + t * ι) (φ + t)) 0) (hR : 0 < R θ φ) :
    HasDerivAt (fun t => boozerThetaB ι V (cylTorus R z) (θ + t * ι) (φ + t))
      (ι * boozerJac B ι (cylTorus R z) θ φ) 0 := by
  have h := (((hasDerivAt_id (0 : ℝ)).mul_const ι).const_add θ).add
    ((hasDerivAt_potential_line hV hL.hasDerivAt hR).const_mul ι)
  convert h using 1
  · funext t; simp [boozerThetaB, boozerPhiB]
  · simp [boozerJac, lineDeriv]; ring

/-- **`J = 1 + v_φ + ι v_θ`** and `a = v_θ` in vacuum, when `v = V ∘ K` is differentiable in
`(θ, φ)` with derivative `L` (`v_θ = L(1, 0)`, `v_φ = L(0, 1)`). -/
theorem boozerJac_eq_partials (hV : VacuumPotentialOn B V (cylTorus R z))
    {L : ℝ × ℝ →L[ℝ] ℝ} (hv : HasFDerivAt (fun p : ℝ × ℝ => V (cylTorus R z p.1 p.2)) L (θ, φ))
    (hθ : DifferentiableAt ℝ (fun t => cylTorus R z t φ) θ)
    (hL : DifferentiableAt ℝ (fun t => cylTorus R z (θ + t * ι) (φ + t)) 0) (hR : 0 < R θ φ) :
    boozerA B (cylTorus R z) θ φ = L (1, 0) ∧
      boozerJac B ι (cylTorus R z) θ φ = 1 + L (0, 1) + ι * L (1, 0) := by
  have h1 : HasDerivAt (fun t => V (cylTorus R z t φ)) (L (1, 0)) θ := by
    have hc : HasDerivAt (fun t : ℝ => (t, φ)) ((1 : ℝ), (0 : ℝ)) θ :=
      (hasDerivAt_id' θ).prodMk (hasDerivAt_const θ φ)
    have := hv.comp_hasDerivAt θ hc
    exact this
  have h2 : HasDerivAt (fun t => V (cylTorus R z (θ + t * ι) (φ + t))) (L (ι, 1)) 0 := by
    have hc : HasDerivAt (fun t : ℝ => (θ + t * ι, φ + t)) (ι, (1 : ℝ)) 0 := by
      have := (((hasDerivAt_id' (0 : ℝ)).mul_const ι).const_add θ).prodMk
        ((hasDerivAt_id' (0 : ℝ)).const_add φ)
      simpa using this
    have := hv.comp_hasDerivAt_of_eq 0 hc (by simp)
    exact this
  have e1 := (hasDerivAt_potential_theta hV hθ.hasDerivAt hR).unique h1
  have e2 := (hasDerivAt_potential_line hV hL.hasDerivAt hR).unique h2
  have hsplit : L (ι, 1) = L (0, 1) + ι * L (1, 0) := by
    rw [show ((ι, 1) : ℝ × ℝ) = (0, 1) + ι • (1, 0) by ext <;> simp, map_add, map_smul,
      smul_eq_mul]
  refine ⟨e1, ?_⟩
  simp only [boozerJac, lineDeriv]
  linarith

/-- The angle data of the degenerate case `V = 0`: `(θ_B, φ_B) = (θ, φ)`. -/
theorem boozerAngles_zero (ι : ℝ) (K : ℝ → ℝ → Space) (θ φ : ℝ) :
    boozerThetaB ι (fun _ => 0) K θ φ = θ ∧ boozerPhiB (fun _ => 0) K θ φ = φ := by
  simp [boozerThetaB, boozerPhiB]

end Cyl

/-! ## The Jacobian identity `J = |B|²/B^φ` on an invariant torus -/

section Jac
variable {B : Space → Space} {R z : ℝ → ℝ → ℝ} {ι : ℝ}

/-- On a `FieldTorus` the toroidal component `B^φ = B · ∇φ` does not vanish, and the field-line
direction is **`𝓛K = B/B^φ`** (invariance). -/
theorem _root_.PlasmaLean.Contract.FieldTorus.lineDeriv_eq (hT : FieldTorus B R z ι) (θ φ : ℝ) :
    toroidalComp B (cylTorus R z) θ φ ≠ 0 ∧
      lineDeriv ι (cylTorus R z) θ φ =
        (toroidalComp B (cylTorus R z) θ φ)⁻¹ • B (cylTorus R z θ φ) := by
  obtain ⟨c, hc⟩ := hT.flow θ φ
  have h1 := inner_toroidal_line (R := R) (z := z) hc (hT.R_pos θ φ)
  rw [inner_smul_right] at h1
  have hc' : c * toroidalComp B (cylTorus R z) θ φ = 1 := h1
  have hne : toroidalComp B (cylTorus R z) θ φ ≠ 0 := by
    intro h; rw [h, mul_zero] at hc'; exact zero_ne_one hc'
  refine ⟨hne, ?_⟩
  have hd : lineDeriv ι (cylTorus R z) θ φ = c • B (cylTorus R z θ φ) := hc.deriv
  rw [hd, eq_inv_of_mul_eq_one_left hc']

/-- On a `FieldTorus`, `B^φ ≠ 0`. -/
theorem _root_.PlasmaLean.Contract.FieldTorus.toroidalComp_ne_zero (hT : FieldTorus B R z ι)
    (θ φ : ℝ) : toroidalComp B (cylTorus R z) θ φ ≠ 0 :=
  (hT.lineDeriv_eq θ φ).1

/-- The torus is differentiable along its field lines. -/
theorem _root_.PlasmaLean.Contract.FieldTorus.differentiableAt_line (hT : FieldTorus B R z ι)
    (θ φ : ℝ) : DifferentiableAt ℝ (fun t => cylTorus R z (θ + t * ι) (φ + t)) 0 := by
  obtain ⟨c, hc⟩ := hT.flow θ φ
  exact hc.differentiableAt

/-- **The Jacobian identity** `J = B · 𝓛K = |B|²/B^φ` on an invariant torus (this uses only
invariance, not the vacuum property). -/
theorem boozerJac_eq_normSq_div (hT : FieldTorus B R z ι) (θ φ : ℝ) :
    boozerJac B ι (cylTorus R z) θ φ =
      ‖B (cylTorus R z θ φ)‖ ^ 2 / toroidalComp B (cylTorus R z) θ φ := by
  rw [boozerJac, (hT.lineDeriv_eq θ φ).2, inner_smul_right, real_inner_self_eq_norm_sq,
    div_eq_inv_mul]

/-- **`J > 0 ⇔ B^φ > 0`** where `B ≠ 0` on an invariant torus. -/
theorem boozerJac_pos_iff (hT : FieldTorus B R z ι) {θ φ : ℝ} (hB : B (cylTorus R z θ φ) ≠ 0) :
    0 < boozerJac B ι (cylTorus R z) θ φ ↔ 0 < toroidalComp B (cylTorus R z) θ φ := by
  rw [boozerJac_eq_normSq_div hT]
  exact div_pos_iff_of_pos_left (by positivity)

/-- `J ≠ 0` where `B ≠ 0` on an invariant torus. -/
theorem boozerJac_ne_zero (hT : FieldTorus B R z ι) {θ φ : ℝ} (hB : B (cylTorus R z θ φ) ≠ 0) :
    boozerJac B ι (cylTorus R z) θ φ ≠ 0 := by
  rw [boozerJac_eq_normSq_div hT]
  exact div_ne_zero (by positivity) (hT.toroidalComp_ne_zero θ φ)

end Jac

/-! ## The Boozer toroidal direction and weak quasisymmetry -/

section Direction
variable {B : Space → Space} {ι : ℝ} {K : ℝ → ℝ → Space}

/-- **`B · e_{φ_B} = 1`** where `J ≠ 0` (in vacuum `B = ∇Φ`, so this is `e_{φ_B} · ∇Φ = 1`, i.e.
`X φ_B = 1` in space form). -/
theorem inner_field_boozerPhiVec {θ φ : ℝ} (hJ : boozerJac B ι K θ φ ≠ 0) :
    ⟪B (K θ φ), boozerPhiVec B ι K θ φ⟫ = 1 := by
  simp only [boozerPhiVec, inner_sub_right, inner_smul_right]
  change (1 + ι * boozerA B K θ φ) / boozerJac B ι K θ φ * boozerJac B ι K θ φ -
    ι * boozerA B K θ φ = 1
  field_simp; ring

/-- **The field form of the Boozer direction** on an invariant torus with `B ≠ 0`:
`e_{φ_B} = B/|B|² − ι (∂_θK − (B·∂_θK/|B|²) B)` (note §1; prototype `boozerVec_eq`). -/
theorem boozerPhiVec_eq_field {R z : ℝ → ℝ → ℝ} (hT : FieldTorus B R z ι) {θ φ : ℝ}
    (hB : B (cylTorus R z θ φ) ≠ 0) :
    boozerPhiVec B ι (cylTorus R z) θ φ =
      (‖B (cylTorus R z θ φ)‖ ^ 2)⁻¹ • B (cylTorus R z θ φ) -
        ι • (thetaDeriv (cylTorus R z) θ φ -
          (boozerA B (cylTorus R z) θ φ / ‖B (cylTorus R z θ φ)‖ ^ 2) • B (cylTorus R z θ φ)) := by
  have hβ := hT.toroidalComp_ne_zero θ φ
  have hn : ‖B (cylTorus R z θ φ)‖ ^ 2 ≠ 0 := by positivity
  rw [boozerPhiVec, boozerJac_eq_normSq_div hT, (hT.lineDeriv_eq θ φ).2, smul_smul]
  set n := ‖B (cylTorus R z θ φ)‖ ^ 2
  set β := toroidalComp B (cylTorus R z) θ φ
  set a := boozerA B (cylTorus R z) θ φ
  have hc : (1 + ι * a) / (n / β) * β⁻¹ = n⁻¹ + ι * (a / n) := by field_simp
  rw [hc, add_smul, smul_sub, smul_smul]
  abel

/-- **`qsError B ξ = torusQADefect`** at a torus point where `ξ = e_{φ_B}`, `|B|` is
differentiable, `K` is differentiable along `θ` and along the field line, and `J ≠ 0`
(note §2, relation 2: the torus defect is the trace of the weak-QS error for the generator
`e_{φ_B}`). -/
theorem qsError_eq_torusQADefect {ξ : Space → Space} {θ φ : ℝ}
    (hB : DifferentiableAt ℝ (fun y => ‖B y‖) (K θ φ))
    (hθ : DifferentiableAt ℝ (fun t => K t φ) θ)
    (hL : DifferentiableAt ℝ (fun t => K (θ + t * ι) (φ + t)) 0)
    (hJ : boozerJac B ι K θ φ ≠ 0) (hξ : ξ (K θ φ) = boozerPhiVec B ι K θ φ) :
    qsError B ξ (K θ φ) = torusQADefect B ι K θ φ := by
  have e1 : thetaDeriv (modB B K) θ φ =
      fderiv ℝ (fun y => ‖B y‖) (K θ φ) (thetaDeriv K θ φ) := by
    have := hB.hasFDerivAt.comp_hasDerivAt θ hθ.hasDerivAt
    exact this.deriv
  have e2 : lineDeriv ι (modB B K) θ φ =
      fderiv ℝ (fun y => ‖B y‖) (K θ φ) (lineDeriv ι K θ φ) := by
    have := hB.hasFDerivAt.comp_hasDerivAt_of_eq 0 hL.hasDerivAt (by simp)
    exact this.deriv
  rw [qsError, hξ, torusQADefect, e1, e2, boozerPhiVec, map_sub, map_smul, map_smul,
    smul_eq_mul, smul_eq_mul, boozerDeriv]
  field_simp

/-- A torus QA bound bounds the weak-QS error `|qsError B ξ|` at every torus point, for any
generator `ξ` equal to `e_{φ_B}` on the torus. -/
theorem qsError_le_of_torusQADefectLe {ξ : Space → Space} {δ : ℝ}
    (h : TorusQADefectLe B ι K δ) (hB : ∀ θ φ, DifferentiableAt ℝ (fun y => ‖B y‖) (K θ φ))
    (hθ : ∀ θ φ, DifferentiableAt ℝ (fun t => K t φ) θ)
    (hL : ∀ θ φ, DifferentiableAt ℝ (fun t => K (θ + t * ι) (φ + t)) 0)
    (hJ : ∀ θ φ, boozerJac B ι K θ φ ≠ 0) (hξ : ∀ θ φ, ξ (K θ φ) = boozerPhiVec B ι K θ φ)
    (θ φ : ℝ) : |qsError B ξ (K θ φ)| ≤ δ := by
  rw [qsError_eq_torusQADefect (hB θ φ) (hθ θ φ) (hL θ φ) (hJ θ φ) (hξ θ φ)]
  exact h θ φ

/-- **The torus defect is controlled by the `δ₂` component of `WeakQSDefect`**: on any set `T`
containing the torus, with a generator equal to `e_{φ_B}` on the torus, `TorusQADefectLe` holds
with `δ = δ₂` (the other two components need a volume; note §2, relation 2). -/
theorem _root_.PlasmaLean.Fields.WeakQSDefect.torusQADefectLe {ξ : Space → Space}
    {ψ : Space → ℝ} {T : Set Space} {δ₀ δ₁ δ₂ : ℝ} (h : WeakQSDefect B ξ ψ T δ₀ δ₁ δ₂)
    (hK : ∀ θ φ, K θ φ ∈ T) (hθ : ∀ θ φ, DifferentiableAt ℝ (fun t => K t φ) θ)
    (hL : ∀ θ φ, DifferentiableAt ℝ (fun t => K (θ + t * ι) (φ + t)) 0)
    (hJ : ∀ θ φ, boozerJac B ι K θ φ ≠ 0) (hξ : ∀ θ φ, ξ (K θ φ) = boozerPhiVec B ι K θ φ) :
    TorusQADefectLe B ι K δ₂ := fun θ φ => by
  rw [← qsError_eq_torusQADefect (h.normB_diff _ (hK θ φ)) (hθ θ φ) (hL θ φ) (hJ θ φ) (hξ θ φ)]
  exact h.qs_le _ (hK θ φ)

end Direction

/-! ## The Boozer guiding-centre model: `symmetryDefect F 0 1 = torusQADefect` -/

section GC
variable {B : Space → Space} {ι : ℝ} {K : ℝ → ℝ → Space}

/-- **Chain rule for the Boozer model on one surface.** If a `BoozerField F` represents `|B|` on
the surface `ψ = ψ₀ > 0` in angles `(TB, PB)` whose derivatives along the torus are those of the
Boozer angles (`∂_θ TB = 1 + ι a`, `∂_θ PB = a`, `𝓛 TB = ι J`, `𝓛 PB = J`), then the
quasi-axisymmetric symmetry defect of the Boozer model is the torus defect:
`symmetryDefect F 0 1 ψ₀ (TB θ φ) (PB θ φ) = F.Bφ = torusQADefect B ι K θ φ`. -/
theorem symmetryDefect_eq_torusQADefect (F : Kinetic.Boozer.BoozerField) {ψ₀ : ℝ}
    (hψ : 0 < ψ₀) {TB PB : ℝ → ℝ → ℝ} {θ φ : ℝ}
    (hF : ∀ θ φ, F.B ψ₀ (TB θ φ) (PB θ φ) = ‖B (K θ φ)‖)
    (hTθ : HasDerivAt (fun t => TB t φ) (1 + ι * boozerA B K θ φ) θ)
    (hPθ : HasDerivAt (fun t => PB t φ) (boozerA B K θ φ) θ)
    (hTL : HasDerivAt (fun t => TB (θ + t * ι) (φ + t)) (ι * boozerJac B ι K θ φ) 0)
    (hPL : HasDerivAt (fun t => PB (θ + t * ι) (φ + t)) (boozerJac B ι K θ φ) 0)
    (hJ : boozerJac B ι K θ φ ≠ 0) :
    Kinetic.Boozer.symmetryDefect F 0 1 ψ₀ (TB θ φ) (PB θ φ) = torusQADefect B ι K θ φ := by
  have hm : modB B K = fun θ φ => F.B ψ₀ (TB θ φ) (PB θ φ) := by
    funext θ φ; exact (hF θ φ).symm
  have hD := F.hasFDerivAt_B (ψ₀, TB θ φ, PB θ φ) hψ
  have e1 : thetaDeriv (modB B K) θ φ =
      F.Bθ ψ₀ (TB θ φ) (PB θ φ) * (1 + ι * boozerA B K θ φ) +
        F.Bφ ψ₀ (TB θ φ) (PB θ φ) * boozerA B K θ φ := by
    have hc := (hasDerivAt_const θ ψ₀).prodMk (hTθ.prodMk hPθ)
    have := hD.comp_hasDerivAt θ hc
    simp only [Kinetic.Boozer.gradCLM_apply] at this
    have h3 : deriv (fun t => F.B ψ₀ (TB t φ) (PB t φ)) θ = _ := this.deriv
    rw [hm, thetaDeriv, h3]; ring
  have e2 : lineDeriv ι (modB B K) θ φ =
      F.Bθ ψ₀ (TB θ φ) (PB θ φ) * (ι * boozerJac B ι K θ φ) +
        F.Bφ ψ₀ (TB θ φ) (PB θ φ) * boozerJac B ι K θ φ := by
    have hc := (hasDerivAt_const (0 : ℝ) ψ₀).prodMk (hTL.prodMk hPL)
    have := hD.comp_hasDerivAt_of_eq 0 hc (by simp)
    simp only [Kinetic.Boozer.gradCLM_apply] at this
    have h3 : deriv (fun t => F.B ψ₀ (TB (θ + t * ι) (φ + t)) (PB (θ + t * ι) (φ + t))) 0 = _ :=
      this.deriv
    rw [hm, lineDeriv, h3]; ring
  rw [torusQADefect, e1, e2, boozerDeriv_comp hJ, Kinetic.Boozer.symmetryDefect]
  ring

/-- **Vacuum form**: on a `FieldTorus` of a vacuum field (`B = ∇φ + ∇V` on the torus, `B ≠ 0`),
a Boozer-model field `F` that represents `|B|` on the surface `ψ₀` in the vacuum Boozer angles
`(θ_B, φ_B)` has `symmetryDefect F 0 1 ψ₀ θ_B φ_B = torusQADefect`. -/
theorem symmetryDefect_eq_torusQADefect_vacuum {V : Space → ℝ} {R z : ℝ → ℝ → ℝ}
    (F : Kinetic.Boozer.BoozerField) {ψ₀ : ℝ} (hψ : 0 < ψ₀) (hT : FieldTorus B R z ι)
    (hV : VacuumPotentialOn B V (cylTorus R z))
    (hθ : ∀ θ φ, DifferentiableAt ℝ (fun t => cylTorus R z t φ) θ)
    (hF : ∀ θ φ, F.B ψ₀ (boozerThetaB ι V (cylTorus R z) θ φ) (boozerPhiB V (cylTorus R z) θ φ) =
      ‖B (cylTorus R z θ φ)‖) {θ φ : ℝ} (hB : B (cylTorus R z θ φ) ≠ 0) :
    Kinetic.Boozer.symmetryDefect F 0 1 ψ₀ (boozerThetaB ι V (cylTorus R z) θ φ)
      (boozerPhiB V (cylTorus R z) θ φ) = torusQADefect B ι (cylTorus R z) θ φ :=
  symmetryDefect_eq_torusQADefect F hψ hF
    (hasDerivAt_boozerThetaB_theta hV (hθ θ φ) (hT.R_pos θ φ))
    (hasDerivAt_boozerPhiB_theta hV (hθ θ φ) (hT.R_pos θ φ))
    (hasDerivAt_boozerThetaB_line hV (hT.differentiableAt_line θ φ) (hT.R_pos θ φ))
    (hasDerivAt_boozerPhiB_line hV (hT.differentiableAt_line θ φ) (hT.R_pos θ φ))
    (boozerJac_ne_zero hT hB)

end GC

/-! ## Global invertibility of the angle change -/

/-- **Global invertibility along a field line** (prototype `DommaschkQSProto`). A continuous
strictly increasing `f : ℝ → ℝ` with `|f x − x| ≤ C` is bijective. -/
theorem bijective_of_strictMono_bdd {f : ℝ → ℝ} {C : ℝ} (hc : Continuous f)
    (hm : StrictMono f) (hb : ∀ x, |f x - x| ≤ C) : Function.Bijective f := by
  refine ⟨hm.injective, hc.surjective ?_ ?_⟩
  · refine Filter.tendsto_atTop_mono (fun x => ?_) (Filter.tendsto_atTop_add_const_right _ (-C)
      Filter.tendsto_id)
    have := (abs_le.1 (hb x)).1; simp only [id]; linarith
  · refine Filter.tendsto_atBot_mono (fun x => ?_) (Filter.tendsto_atBot_add_const_right _ C
      Filter.tendsto_id)
    have := (abs_le.1 (hb x)).2; simp only [id]; linarith

/-- Rejected fixture for the bound hypothesis of `bijective_of_strictMono_bdd`: the strictly
increasing map `x ↦ 2x` is not within distance `1` of the identity. -/
theorem not_bdd_double : ¬ ∀ x : ℝ, |2 * x - x| ≤ 1 := by
  intro h; have := h 2; norm_num [abs_of_pos] at this

/-- **The angle map is a bijection of `ℝ²`.** With `v` bounded and, along every line
`s ↦ (α + s ι, s)`, `s ↦ s + v(α + s ι, s)` differentiable with positive derivative `j`, the map
`(θ, φ) ↦ (θ + ι v, φ + v)` is bijective. (It preserves `θ − ι φ`, and on each fibre it is a
strictly increasing map within `C` of the identity.) -/
theorem bijective_angleMap {ι C : ℝ} {v j : ℝ → ℝ → ℝ}
    (hd : ∀ α s, HasDerivAt (fun s => s + v (α + s * ι) s) (j (α + s * ι) s) s)
    (hj : ∀ θ φ, 0 < j θ φ) (hb : ∀ θ φ, |v θ φ| ≤ C) :
    Function.Bijective (fun p : ℝ × ℝ => (p.1 + ι * v p.1 p.2, p.2 + v p.1 p.2)) := by
  have hfib : ∀ α, Function.Bijective (fun s => s + v (α + s * ι) s) := fun α =>
    bijective_of_strictMono_bdd
      (continuous_iff_continuousAt.2 fun s => (hd α s).continuousAt)
      (strictMono_of_hasDerivAt_pos (hd α) fun s => hj _ _)
      (fun s => by simpa using hb (α + s * ι) s)
  refine ⟨fun p q hpq => ?_, fun ab => ?_⟩
  · simp only [Prod.mk.injEq] at hpq
    obtain ⟨h1, h2⟩ := hpq
    set α := p.1 - ι * p.2
    have hp1 : p.1 = α + p.2 * ι := by simp only [α]; ring
    have hq1 : q.1 = α + q.2 * ι := by simp only [α]; linear_combination -h1 + ι * h2
    have h22 : p.2 = q.2 := (hfib α).1 (by
      simp only; rw [← hp1, ← hq1]; exact h2)
    exact Prod.ext (by rw [hp1, hq1, h22]) h22
  · obtain ⟨s, hs⟩ := (hfib (ab.1 - ι * ab.2)).2 ab.2
    simp only at hs
    refine ⟨(ab.1 - ι * ab.2 + s * ι, s), Prod.ext ?_ ?_⟩
    · simp only
      linear_combination ι * hs
    · exact hs

section Bij
variable {B : Space → Space} {V : Space → ℝ} {R z : ℝ → ℝ → ℝ} {ι : ℝ}

/-- Shifting the base point of a line derivative: the derivative of `t ↦ f(θ + t ι, φ + t)` at
`0`, with `(θ, φ) = (α + s ι, s)`, is the derivative of `s' ↦ f(α + s' ι, s')` at `s`. -/
theorem hasDerivAt_line_shift {f : ℝ → ℝ → ℝ} {d α s : ℝ}
    (h : HasDerivAt (fun t => f (α + s * ι + t * ι) (s + t)) d 0) :
    HasDerivAt (fun s' => f (α + s' * ι) s') d s := by
  have h' := HasDerivAt.comp_sub_const s s (by simpa using h)
  convert h' using 1
  funext t
  rw [show α + s * ι + (t - s) * ι = α + t * ι by ring, show s + (t - s) = t by ring]

/-- **Bijectivity of the vacuum Boozer angle change** `(θ, φ) ↦ (θ_B, φ_B)` on `ℝ²`, on a
`FieldTorus` of a vacuum field with `J > 0` and `V ∘ K` bounded (note §1: along each field line
`∂φ_B/∂φ|_α = J > 0`, and `φ_B − φ = v` is bounded). The map commutes with the period
translations when `v` is periodic, so it also induces a bijection of the torus. -/
theorem boozerAngles_bijective {C : ℝ} (hT : FieldTorus B R z ι)
    (hV : VacuumPotentialOn B V (cylTorus R z))
    (hJ : ∀ θ φ, 0 < boozerJac B ι (cylTorus R z) θ φ)
    (hb : ∀ θ φ, |V (cylTorus R z θ φ)| ≤ C) :
    Function.Bijective (fun p : ℝ × ℝ =>
      (boozerThetaB ι V (cylTorus R z) p.1 p.2, boozerPhiB V (cylTorus R z) p.1 p.2)) := by
  have hmap : (fun p : ℝ × ℝ =>
      (boozerThetaB ι V (cylTorus R z) p.1 p.2, boozerPhiB V (cylTorus R z) p.1 p.2)) =
      fun p : ℝ × ℝ => (p.1 + ι * V (cylTorus R z p.1 p.2), p.2 + V (cylTorus R z p.1 p.2)) := by
    funext p; simp [boozerThetaB, boozerPhiB]
  rw [hmap]
  refine bijective_angleMap (v := fun θ φ => V (cylTorus R z θ φ))
    (j := boozerJac B ι (cylTorus R z)) (fun α s => ?_) hJ hb
  have h := hasDerivAt_boozerPhiB_line hV (hT.differentiableAt_line (α + s * ι) s)
    (hT.R_pos _ _)
  exact hasDerivAt_line_shift (f := fun θ φ => φ + V (cylTorus R z θ φ)) h

end Bij

/-! ## The QA characterisation -/

/-- A continuous linear functional on `ℝ²` in coordinates. -/
theorem clm_apply_pair (L : ℝ × ℝ →L[ℝ] ℝ) (a b : ℝ) : L (a, b) = a * L (1, 0) + b * L (0, 1) := by
  rw [show ((a, b) : ℝ × ℝ) = a • (1, 0) + b • (0, 1) by ext <;> simp, map_add, map_smul,
    map_smul, smul_eq_mul, smul_eq_mul]

/-- **The abstract 2-D step of the QA characterisation (mixed chart).** Let `f, T : ℝ² → ℝ` be
differentiable, with `∂_θ T ≥ m > 0` and `|∂_φ T| ≤ M`, and let `f` be constant along the
kernel direction `(−∂_φ T, ∂_θ T)` of `dT`. Then `f` is a function of `T`. (For each `φ` the map
`θ ↦ T(θ, φ)` is a bijection of `ℝ`; its inverse `Θ(c, φ)` is Lipschitz and differentiable in
`φ`, and `φ ↦ f(Θ(c, φ), φ)` has derivative `0`.) -/
theorem exists_comp_of_kernel {f T : ℝ × ℝ → ℝ} {df dT : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ)} {m M : ℝ}
    (hf : ∀ p, HasFDerivAt f (df p) p) (hT : ∀ p, HasFDerivAt T (dT p) p)
    (hm0 : 0 < m) (hm : ∀ p, m ≤ dT p (1, 0)) (hM : ∀ p, |dT p (0, 1)| ≤ M)
    (hker : ∀ p, df p (-(dT p (0, 1)), dT p (1, 0)) = 0) :
    ∃ F : ℝ → ℝ, ∀ p, f p = F (T p) := by
  -- partial derivatives of `T`
  have hTθ : ∀ θ φ, HasDerivAt (fun t => T (t, φ)) (dT (θ, φ) (1, 0)) θ := fun θ φ => by
    have hc : HasDerivAt (fun t : ℝ => (t, φ)) ((1 : ℝ), (0 : ℝ)) θ :=
      (hasDerivAt_id' θ).prodMk (hasDerivAt_const θ φ)
    exact (hT (θ, φ)).comp_hasDerivAt θ hc
  have hTφ : ∀ θ φ, HasDerivAt (fun t => T (θ, t)) (dT (θ, φ) (0, 1)) φ := fun θ φ => by
    have hc : HasDerivAt (fun t : ℝ => (θ, t)) ((0 : ℝ), (1 : ℝ)) φ :=
      (hasDerivAt_const φ θ).prodMk (hasDerivAt_id' φ)
    exact (hT (θ, φ)).comp_hasDerivAt φ hc
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (0, 0))
  -- growth in `θ`
  have hgrow : ∀ φ θ θ', θ ≤ θ' → m * (θ' - θ) ≤ T (θ', φ) - T (θ, φ) := by
    intro φ θ θ' h
    have hmono : Monotone fun t => T (t, φ) - m * t :=
      monotone_of_hasDerivAt_nonneg (f' := fun t => dT (t, φ) (1, 0) - m)
        (fun t => by
          have h : HasDerivAt (fun t => T (t, φ) - m * t) (dT (t, φ) (1, 0) - m * 1) t :=
            (hTθ t φ).sub ((hasDerivAt_id' t).const_mul m)
          simpa using h)
        (fun t => by simpa using hm (t, φ))
    have := hmono h
    simp only at this
    linarith
  have hstrict : ∀ φ, StrictMono fun t => T (t, φ) := fun φ =>
    strictMono_of_hasDerivAt_pos (fun t => hTθ t φ) fun t => hm0.trans_le (hm (t, φ))
  have hsurj : ∀ φ, Function.Surjective fun t => T (t, φ) := by
    intro φ
    refine Continuous.surjective (continuous_iff_continuousAt.2 fun t => (hTθ t φ).continuousAt)
      ?_ ?_
    · refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_left _ (T (0, φ))
        (tendsto_id.const_mul_atTop hm0))
      filter_upwards [eventually_ge_atTop 0] with t ht
      have := hgrow φ 0 t ht; simp only [id]; linarith
    · refine tendsto_atBot_mono' _ ?_ (tendsto_atBot_add_const_left _ (T (0, φ))
        (tendsto_id.const_mul_atBot hm0))
      filter_upwards [eventually_le_atBot 0] with t ht
      have := hgrow φ t 0 ht; simp only [id]; linarith
  -- the inverse in `θ`
  let Θ : ℝ → ℝ → ℝ := fun c φ => Function.surjInv (hsurj φ) c
  have hΘ : ∀ c φ, T (Θ c φ, φ) = c := fun c φ => Function.surjInv_eq (hsurj φ) c
  have hΘT : ∀ p : ℝ × ℝ, Θ (T p) p.2 = p.1 := fun p =>
    (hstrict p.2).injective (hΘ (T p) p.2)
  -- Lipschitz in `φ`
  have hlip : ∀ c φ φ', m * |Θ c φ' - Θ c φ| ≤ M * |φ' - φ| := by
    intro c φ φ'
    set θ₁ := Θ c φ
    set θ₂ := Θ c φ'
    have hlow : m * |θ₂ - θ₁| ≤ |T (θ₂, φ) - T (θ₁, φ)| := by
      rcases le_total θ₁ θ₂ with h | h
      · rw [abs_of_nonneg (sub_nonneg.2 h)]
        exact (hgrow φ θ₁ θ₂ h).trans (le_abs_self _)
      · rw [abs_of_nonpos (sub_nonpos.2 h), abs_sub_comm]
        have := hgrow φ θ₂ θ₁ h
        exact (by linarith : m * -(θ₂ - θ₁) ≤ T (θ₁, φ) - T (θ₂, φ)).trans (le_abs_self _)
    have hup : |T (θ₂, φ') - T (θ₂, φ)| ≤ M * |φ' - φ| := by
      have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.univ)
        (f := fun t => T (θ₂, t)) (fun t _ => (hTφ θ₂ t).hasDerivWithinAt)
        (fun t _ => by simpa using hM (θ₂, t)) convex_univ (Set.mem_univ φ) (Set.mem_univ φ')
      simpa [Real.norm_eq_abs] using this
    have e : T (θ₂, φ') = T (θ₁, φ) := by rw [hΘ, hΘ]
    rw [e] at hup
    rw [abs_sub_comm] at hup
    linarith
  -- differentiability of `Θ c` in `φ`
  have hΘd : ∀ c s, HasDerivAt (Θ c)
      (-(dT (Θ c s, s) (0, 1)) / dT (Θ c s, s) (1, 0)) s := by
    intro c s
    set p : ℝ × ℝ := (Θ c s, s)
    set α := dT p (1, 0)
    set β := dT p (0, 1)
    have hα : α ≠ 0 := (hm0.trans_le (hm p)).ne'
    have hb : ∀ s', |Θ c s' - Θ c s| ≤ (M / m) * |s' - s| := fun s' => by
      rw [div_mul_eq_mul_div, le_div_iff₀ hm0, mul_comm]; exact hlip c s s'
    have hcont : Tendsto (fun s' => ((Θ c s', s') : ℝ × ℝ)) (𝓝 s) (𝓝 p) := by
      have hΘc : Tendsto (Θ c) (𝓝 s) (𝓝 (Θ c s)) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        refine squeeze_zero (fun _ => norm_nonneg _) (fun s' => ?_) (g := fun s' => (M / m) *
          ‖s' - s‖) ?_
        · simpa [Real.norm_eq_abs] using hb s'
        · have : Tendsto (fun s' : ℝ => ‖s' - s‖) (𝓝 s) (𝓝 0) := by
            simpa using (continuous_id.sub continuous_const).norm.tendsto' s _ (by simp)
          simpa using this.const_mul (M / m)
      exact hΘc.prodMk_nhds tendsto_id
    have hO : (fun s' => ((Θ c s', s') : ℝ × ℝ) - p) =O[𝓝 s] fun s' => s' - s := by
      refine Asymptotics.IsBigO.of_bound (M / m + 1) (Eventually.of_forall fun s' => ?_)
      rw [norm_prod_le_iff]
      have hMm : 0 ≤ M / m := div_nonneg hM0 hm0.le
      simp only [Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs, p]
      constructor
      · nlinarith [hb s', abs_nonneg (s' - s)]
      · nlinarith [abs_nonneg (s' - s)]
    have ho := (((hT p).isLittleO.comp_tendsto hcont).trans_isBigO hO).const_mul_left (-α⁻¹)
    rw [hasDerivAt_iff_isLittleO]
    refine ho.congr_left fun s' => ?_
    simp only [Function.comp_apply, hΘ, p]
    rw [clm_apply_pair]
    simp only [Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
    change -α⁻¹ * (c - c - ((Θ c s' - Θ c s) * α + (s' - s) * β)) =
      Θ c s' - Θ c s - (s' - s) * (-β / α)
    field_simp
    ring
  -- `φ ↦ f(Θ(c, φ), φ)` is constant
  have hconst : ∀ c s s', f (Θ c s, s) = f (Θ c s', s') := by
    intro c
    have hd : ∀ s, HasDerivAt (fun s => f (Θ c s, s)) 0 s := by
      intro s
      have hc := (hΘd c s).prodMk (hasDerivAt_id' s)
      have := HasFDerivAt.comp_hasDerivAt (f := fun x => (Θ c x, x)) s (hf (Θ c s, s)) hc
      have hα : dT (Θ c s, s) (1, 0) ≠ 0 := (hm0.trans_le (hm _)).ne'
      have hk := hker (Θ c s, s)
      have key : df (Θ c s, s) (-(dT (Θ c s, s)) (0, 1) / (dT (Θ c s, s)) (1, 0), 1) = 0 := by
        rw [clm_apply_pair] at hk ⊢
        field_simp
        linear_combination hk
      exact this.congr_deriv key
    exact is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) fun s => (hd s).deriv
  refine ⟨fun c => f (Θ c 0, 0), fun p => ?_⟩
  have := hconst (T p) p.2 0
  rw [hΘT p] at this
  exact this

section QA
variable {B : Space → Space} {V : Space → ℝ} {R z : ℝ → ℝ → ℝ} {ι : ℝ}

/-- The `θ`-partial of a function differentiable on `ℝ²`. -/
theorem hasDerivAt_theta_of_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : ℝ × ℝ → E} {L : ℝ × ℝ →L[ℝ] E} {θ φ : ℝ} (h : HasFDerivAt G L (θ, φ)) :
    HasDerivAt (fun t => G (t, φ)) (L (1, 0)) θ := by
  have hc : HasDerivAt (fun t : ℝ => (t, φ)) ((1 : ℝ), (0 : ℝ)) θ :=
    (hasDerivAt_id' θ).prodMk (hasDerivAt_const θ φ)
  exact h.comp_hasDerivAt θ hc

/-- The line derivative `𝓛` of a function differentiable on `ℝ²` is `L(ι, 1)`. -/
theorem hasDerivAt_line_of_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : ℝ × ℝ → E} {L : ℝ × ℝ →L[ℝ] E} {θ φ : ℝ} (h : HasFDerivAt G L (θ, φ)) :
    HasDerivAt (fun t => G (θ + t * ι, φ + t)) (L (ι, 1)) 0 := by
  have hc : HasDerivAt (fun t : ℝ => (θ + t * ι, φ + t)) (ι, (1 : ℝ)) 0 := by
    have := (((hasDerivAt_id' (0 : ℝ)).mul_const ι).const_add θ).prodMk
      ((hasDerivAt_id' (0 : ℝ)).const_add φ)
    simpa using this
  exact h.comp_hasDerivAt_of_eq 0 hc (by simp)

/-- **Exact QA has zero defect** (direction ⇐ of the QA characterisation): on a `FieldTorus`
of a vacuum field, if `|B| ∘ K = F ∘ θ_B` with `F` differentiable, then `torusQADefect = 0`. -/
theorem torusQADefect_eq_zero_of_qa (hT : FieldTorus B R z ι)
    (hV : VacuumPotentialOn B V (cylTorus R z)) {θ φ : ℝ}
    (hθ : DifferentiableAt ℝ (fun t => cylTorus R z t φ) θ) {F : ℝ → ℝ}
    (hQA : ∀ θ φ, ‖B (cylTorus R z θ φ)‖ = F (boozerThetaB ι V (cylTorus R z) θ φ))
    (hF : DifferentiableAt ℝ F (boozerThetaB ι V (cylTorus R z) θ φ)) :
    torusQADefect B ι (cylTorus R z) θ φ = 0 := by
  have hm : modB B (cylTorus R z) = fun θ φ => F (boozerThetaB ι V (cylTorus R z) θ φ) := by
    funext θ φ; exact hQA θ φ
  have e1 : thetaDeriv (modB B (cylTorus R z)) θ φ =
      deriv F (boozerThetaB ι V (cylTorus R z) θ φ) * (1 + ι * boozerA B (cylTorus R z) θ φ) := by
    have := hF.hasDerivAt.comp θ (hasDerivAt_boozerThetaB_theta hV hθ (hT.R_pos θ φ))
    rw [hm]; exact this.deriv
  have e2 : lineDeriv ι (modB B (cylTorus R z)) θ φ =
      deriv F (boozerThetaB ι V (cylTorus R z) θ φ) * (ι * boozerJac B ι (cylTorus R z) θ φ) := by
    have := hF.hasDerivAt.comp_of_eq 0
      (hasDerivAt_boozerThetaB_line hV (hT.differentiableAt_line θ φ) (hT.R_pos θ φ)) (by simp)
    rw [hm]; exact this.deriv
  rw [torusQADefect, e1, e2, boozerDeriv_qa]

/-- **Zero defect implies exact QA** (direction ⇒, mixed chart): for a vacuum field on a torus
`K` differentiable on `ℝ²`, with `|B| ∘ K` differentiable, `J ≠ 0`, `∂_θ θ_B = 1 + ι a ≥ m > 0`
and `|∂_φ θ_B| = |ι v_φ| = |ι (J − 1 − ι a)| ≤ M`, if `torusQADefect ≡ 0` then
`|B| ∘ K = F ∘ θ_B` for some `F : ℝ → ℝ`. -/
theorem exists_qa_of_torusQADefect_eq_zero {m M : ℝ}
    (hV : VacuumPotentialOn B V (cylTorus R z)) (hR : ∀ θ φ, 0 < R θ φ)
    (hK : ∀ p : ℝ × ℝ, DifferentiableAt ℝ (fun p : ℝ × ℝ => cylTorus R z p.1 p.2) p)
    (hf : ∀ p : ℝ × ℝ, DifferentiableAt ℝ (fun p : ℝ × ℝ => ‖B (cylTorus R z p.1 p.2)‖) p)
    (hm0 : 0 < m) (hm : ∀ θ φ, m ≤ 1 + ι * boozerA B (cylTorus R z) θ φ)
    (hM : ∀ θ φ, |ι * (boozerJac B ι (cylTorus R z) θ φ - 1 -
      ι * boozerA B (cylTorus R z) θ φ)| ≤ M)
    (hJ : ∀ θ φ, boozerJac B ι (cylTorus R z) θ φ ≠ 0)
    (h0 : ∀ θ φ, torusQADefect B ι (cylTorus R z) θ φ = 0) :
    ∃ F : ℝ → ℝ, ∀ θ φ, ‖B (cylTorus R z θ φ)‖ = F (boozerThetaB ι V (cylTorus R z) θ φ) := by
  set K := cylTorus R z with hKdef
  let v : ℝ × ℝ → ℝ := fun p => V (K p.1 p.2)
  have hvd : ∀ p, HasFDerivAt v (fderiv ℝ v p) p := fun p =>
    ((hV p.1 p.2).differentiableAt.comp p (hK p)).hasFDerivAt
  have hKd : ∀ p, HasFDerivAt (fun p : ℝ × ℝ => K p.1 p.2)
      (fderiv ℝ (fun p : ℝ × ℝ => K p.1 p.2) p) p :=
    fun p => (hK p).hasFDerivAt
  -- `a = v_θ`, `J = 1 + v_φ + ι v_θ`
  have hpart : ∀ θ φ, boozerA B K θ φ = fderiv ℝ v (θ, φ) (1, 0) ∧
      boozerJac B ι K θ φ = 1 + fderiv ℝ v (θ, φ) (0, 1) + ι * fderiv ℝ v (θ, φ) (1, 0) :=
    fun θ φ => boozerJac_eq_partials hV (hvd (θ, φ))
      (hasDerivAt_theta_of_hasFDerivAt (hKd (θ, φ))).differentiableAt
      (hasDerivAt_line_of_hasFDerivAt (ι := ι) (hKd (θ, φ))).differentiableAt (hR θ φ)
  let T : ℝ × ℝ → ℝ := fun p => p.1 + ι * v p
  let dT : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fun p =>
    ContinuousLinearMap.fst ℝ ℝ ℝ + ι • fderiv ℝ v p
  have hT : ∀ p, HasFDerivAt T (dT p) p := fun p =>
    (hasFDerivAt_fst).add ((hvd p).const_mul ι)
  let f : ℝ × ℝ → ℝ := fun p => ‖B (K p.1 p.2)‖
  have hfd : ∀ p, HasFDerivAt f (fderiv ℝ f p) p := fun p => (hf p).hasFDerivAt
  obtain ⟨F, hF⟩ := exists_comp_of_kernel (f := f) (T := T) (m := m) (M := M) hfd hT hm0
    (fun p => by
      have := hm p.1 p.2
      rw [(hpart p.1 p.2).1] at this
      simpa [dT] using this)
    (fun p => by
      have := hM p.1 p.2
      rw [(hpart p.1 p.2).1, (hpart p.1 p.2).2] at this
      simp only [dT, add_apply, ContinuousLinearMap.coe_fst',
        FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
      convert this using 2; ring)
    (fun p => by
      obtain ⟨ha, hj⟩ := hpart p.1 p.2
      have hd := h0 p.1 p.2
      have e1 : thetaDeriv (modB B K) p.1 p.2 = fderiv ℝ f p (1, 0) :=
        (hasDerivAt_theta_of_hasFDerivAt (hfd (p.1, p.2))).deriv
      have e2 : lineDeriv ι (modB B K) p.1 p.2 = fderiv ℝ f p (ι, 1) :=
        (hasDerivAt_line_of_hasFDerivAt (hfd (p.1, p.2))).deriv
      rw [torusQADefect, e1, e2, boozerDeriv, div_eq_zero_iff] at hd
      have hd' := hd.resolve_right (hJ p.1 p.2)
      rw [ha, hj, clm_apply_pair (fderiv ℝ f p) ι 1] at hd'
      simp only [dT, add_apply, ContinuousLinearMap.coe_fst',
        FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [clm_apply_pair]
      linear_combination hd')
  refine ⟨F, fun θ φ => ?_⟩
  have := hF (θ, φ)
  simp only [f, T, v] at this
  rw [this]
  congr 1
  simp [boozerThetaB, boozerPhiB]

end QA

/-! ## Sanity triad -/

section Sanity

/-- `r² = ρ²` at a cylindrical point. -/
theorem r2_cylPoint (ρ φ ζ : ℝ) : r2 (cylPoint ρ φ ζ) = ρ ^ 2 := by
  simp only [r2, cylPoint, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination ρ ^ 2 * sin_sq_add_cos_sq φ

/-- `∇φ = (−sin φ, cos φ, 0)/ρ` at a cylindrical point with `ρ > 0`. -/
theorem toroidal_cylPoint {ρ : ℝ} (hρ : 0 < ρ) (φ ζ : ℝ) :
    toroidal (cylPoint ρ φ ζ) = toLp 2 ![-sin φ / ρ, cos φ / ρ, 0] := by
  have hw : winv (cylPoint ρ φ ζ) = (ρ ^ 2)⁻¹ := by rw [winv, r2_cylPoint]
  simp only [toroidal, hw]
  ext i
  fin_cases i <;> simp [cylPoint] <;> field_simp

/-- `|∇φ| = 1/ρ`. -/
theorem norm_toroidal_cylPoint {ρ : ℝ} (hρ : 0 < ρ) (φ ζ : ℝ) :
    ‖toroidal (cylPoint ρ φ ζ)‖ = ρ⁻¹ := by
  rw [toroidal_cylPoint hρ, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  have h : ‖-sin φ / ρ‖ ^ 2 + ‖cos φ / ρ‖ ^ 2 + ‖(0 : ℝ)‖ ^ 2 = (ρ⁻¹) ^ 2 := by
    simp only [Real.norm_eq_abs, sq_abs, norm_zero]
    field_simp
    linear_combination sin_sq_add_cos_sq φ
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  rw [h, Real.sqrt_sq (inv_nonneg.2 hρ.le)]

/-- The circles of constant `(ρ, ζ)` are the field lines of `∇φ`:
`d/dt cylPoint ρ (φ + t) ζ = ρ² ∇φ`. -/
theorem hasDerivAt_cylPoint_phi {ρ : ℝ} (hρ : 0 < ρ) (φ ζ : ℝ) :
    HasDerivAt (fun t => cylPoint ρ (φ + t) ζ) (ρ ^ 2 • toroidal (cylPoint ρ φ ζ)) 0 := by
  have h0 : HasDerivAt (fun t => ρ * cos (φ + t)) (ρ * -sin φ) 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_add φ).cos.const_mul ρ
  have h1 : HasDerivAt (fun t => ρ * sin (φ + t)) (ρ * cos φ) 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_add φ).sin.const_mul ρ
  have h := hasDerivAt_space3 h0 h1 (hasDerivAt_const (0 : ℝ) ζ)
  rw [toroidal_cylPoint hρ]
  refine h.congr_deriv ?_
  ext i
  fin_cases i <;> simp <;> field_simp

/-- The **circular torus** `R = R₀ + r cos θ`. -/
@[expose] def circR (R₀ r : ℝ) (θ _φ : ℝ) : ℝ := R₀ + r * cos θ

/-- The **circular torus** `z = r sin θ`. -/
@[expose] def circZ (r : ℝ) (θ _φ : ℝ) : ℝ := r * sin θ

/-- The circular torus stays off the axis when `0 < r < R₀`. -/
theorem circR_pos {R₀ r : ℝ} (hr : 0 < r) (hR : r < R₀) (θ φ : ℝ) : 0 < circR R₀ r θ φ := by
  unfold circR; nlinarith [neg_one_le_cos θ]

/-- Along the line `t ↦ (θ, φ + t)` (`ι = 0`) the circular torus moves along the circle of
`∇φ`. -/
theorem hasDerivAt_circ_line {R₀ r : ℝ} (hr : 0 < r) (hR : r < R₀) (θ φ : ℝ) :
    HasDerivAt (fun t => cylTorus (circR R₀ r) (circZ r) (θ + t * 0) (φ + t))
      (circR R₀ r θ φ ^ 2 • toroidal (cylTorus (circR R₀ r) (circZ r) θ φ)) 0 := by
  have h := hasDerivAt_cylPoint_phi (circR_pos hr hR θ φ) φ (circZ r θ φ)
  simpa [cylTorus, circR, circZ] using h

/-- The circular torus as a `FieldTorus` of a field `B = λ ∇φ` (`λ ≠ 0` on the torus), with
rotation number `0`. -/
theorem circ_fieldTorus {B : Space → Space} {R₀ r : ℝ} (hr : 0 < r) (hR : r < R₀)
    (lam : ℝ → ℝ → ℝ) (hlam : ∀ θ φ, lam θ φ ≠ 0)
    (hB : ∀ θ φ, B (cylTorus (circR R₀ r) (circZ r) θ φ) =
      lam θ φ • toroidal (cylTorus (circR R₀ r) (circZ r) θ φ)) :
    FieldTorus B (circR R₀ r) (circZ r) 0 where
  continuous_R := by unfold circR; fun_prop
  continuous_z := by unfold circZ; fun_prop
  R_pos := circR_pos hr hR
  per_θ_R θ φ := by simp [circR]
  per_θ_z θ φ := by simp [circZ]
  per_φ_R θ φ := rfl
  per_φ_z θ φ := rfl
  flow θ φ := by
    refine ⟨circR R₀ r θ φ ^ 2 / lam θ φ, ?_⟩
    have h := hasDerivAt_circ_line hr hR θ φ
    change HasDerivAt (fun t => cylTorus (circR R₀ r) (circZ r) (θ + t * 0) (φ + t))
      ((circR R₀ r θ φ ^ 2 / lam θ φ) • B (cylTorus (circR R₀ r) (circZ r) θ φ)) 0
    rw [hB, smul_smul, div_mul_cancel₀ _ (hlam θ φ)]
    exact h

/-- **Accepted fixture (axisymmetric)**: the circular torus is a `FieldTorus` of the vacuum
field `∇φ`, with rotation number `0`. -/
theorem circle_fieldTorus {R₀ r : ℝ} (hr : 0 < r) (hR : r < R₀) :
    FieldTorus toroidal (circR R₀ r) (circZ r) 0 :=
  circ_fieldTorus hr hR (fun _ _ => 1) (fun _ _ => one_ne_zero) (fun _ _ => (one_smul _ _).symm)

/-- `∇φ` is a vacuum field in the sense of `VacuumPotentialOn`, with `V = 0`. -/
theorem vacuumPotentialOn_toroidal (K : ℝ → ℝ → Space) :
    VacuumPotentialOn toroidal (fun _ => 0) K := fun θ φ => by
  rw [sub_self, map_zero]; exact hasFDerivAt_const 0 _

/-- **Normalisation**: for `B = ∇φ` on any cylindrical torus (`R > 0`), `J = 1` and `a = 0`. -/
theorem boozerJac_toroidal {R z : ℝ → ℝ → ℝ} {ι θ φ : ℝ} (hR : 0 < R θ φ)
    (hθ : DifferentiableAt ℝ (fun t => cylTorus R z t φ) θ)
    (hL : DifferentiableAt ℝ (fun t => cylTorus R z (θ + t * ι) (φ + t)) 0) :
    boozerJac toroidal ι (cylTorus R z) θ φ = 1 ∧ boozerA toroidal (cylTorus R z) θ φ = 0 :=
  ⟨inner_toroidal_line hL.hasDerivAt hR, inner_toroidal_theta hθ.hasDerivAt hR⟩

/-- **Accepted fixture**: the axisymmetric circular torus of `∇φ` has zero QA defect
(`|B| = 1/(R₀ + r cos θ)` does not depend on `φ`). -/
theorem torusQADefect_circle {R₀ r : ℝ} (hr : 0 < r) (hR : r < R₀) (θ φ : ℝ) :
    torusQADefect toroidal 0 (cylTorus (circR R₀ r) (circZ r)) θ φ = 0 := by
  have hm : modB toroidal (cylTorus (circR R₀ r) (circZ r)) = fun θ _ => (R₀ + r * cos θ)⁻¹ := by
    funext θ φ
    exact norm_toroidal_cylPoint (circR_pos hr hR θ φ) _ _
  have hL : lineDeriv 0 (modB toroidal (cylTorus (circR R₀ r) (circZ r))) θ φ = 0 := by
    rw [hm, lineDeriv]; simp
  rw [torusQADefect, hL, boozerDeriv]; simp

/-- The **rippled toroidal field** `(1 + ε cos φ) ∇φ` (with `cos φ = x/√(x² + y²)`): it has the
circles of constant `(R, z)` as field lines (`ripple_fieldTorus`) but `|B|` varies along them.
It is not a vacuum field (`∇ × B ≠ 0` for `ε ≠ 0`); it is the rejected fixture of the defect. -/
@[expose] def rippleField (ε : ℝ) (y : Space) : Space :=
  (1 + ε * (y 0 * √(winv y))) • toroidal y

/-- The ripple factor `1 + ε cos φ` is positive for `|ε| < 1`. -/
theorem ripple_pos {ε : ℝ} (hε : |ε| < 1) (φ : ℝ) : 0 < 1 + ε * cos φ := by
  have h : |ε * cos φ| ≤ |ε| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one φ)
  linarith [neg_abs_le (ε * cos φ)]

/-- `rippleField ε = (1 + ε cos φ) ∇φ` at a cylindrical point. -/
theorem rippleField_cylPoint (ε : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (φ ζ : ℝ) :
    rippleField ε (cylPoint ρ φ ζ) = (1 + ε * cos φ) • toroidal (cylPoint ρ φ ζ) := by
  have hw : √(winv (cylPoint ρ φ ζ)) = ρ⁻¹ := by
    rw [winv, r2_cylPoint, ← inv_pow, Real.sqrt_sq (inv_nonneg.2 hρ.le)]
  rw [rippleField, hw]
  congr 2
  simp only [cylPoint, PiLp.toLp_apply, Matrix.cons_val_zero]
  field_simp

/-- The circular torus is an invariant torus of the rippled field (`|ε| < 1`), with `ι = 0`. -/
theorem ripple_fieldTorus {ε R₀ r : ℝ} (hε : |ε| < 1) (hr : 0 < r) (hR : r < R₀) :
    FieldTorus (rippleField ε) (circR R₀ r) (circZ r) 0 :=
  circ_fieldTorus hr hR (fun _ φ => 1 + ε * cos φ)
    (fun _ φ => (ripple_pos hε φ).ne')
    (fun θ φ => rippleField_cylPoint ε (circR_pos hr hR θ φ) _ _)

/-- The defect of the rippled field on the circular torus (`ι = 0`):
`∂_{φ_B}|B| = −ε sin φ / ((R₀ + r cos θ)(1 + ε cos φ))`. -/
theorem torusQADefect_ripple {ε R₀ r : ℝ} (hε : |ε| < 1) (hr : 0 < r) (hR : r < R₀)
    (θ φ : ℝ) :
    torusQADefect (rippleField ε) 0 (cylTorus (circR R₀ r) (circZ r)) θ φ =
      -(ε * sin φ) / ((R₀ + r * cos θ) * (1 + ε * cos φ)) := by
  have hρ := circR_pos hr hR θ φ
  have hm : modB (rippleField ε) (cylTorus (circR R₀ r) (circZ r)) =
      fun θ φ => (1 + ε * cos φ) * (R₀ + r * cos θ)⁻¹ := by
    funext θ φ
    simp only [modB, cylTorus]
    rw [rippleField_cylPoint ε (circR_pos hr hR θ φ), norm_smul,
      norm_toroidal_cylPoint (circR_pos hr hR θ φ), Real.norm_eq_abs,
      abs_of_pos (ripple_pos hε φ), circR]
  have hL : lineDeriv 0 (modB (rippleField ε) (cylTorus (circR R₀ r) (circZ r))) θ φ =
      -(ε * sin φ) * (R₀ + r * cos θ)⁻¹ := by
    rw [hm, lineDeriv]
    simp only [mul_zero, add_zero]
    have h := ((((hasDerivAt_id' (0 : ℝ)).const_add φ).cos.const_mul ε).const_add 1).mul_const
      ((R₀ + r * cos θ)⁻¹)
    simp only [add_zero, mul_one] at h
    rw [h.deriv]; ring
  have hJ : boozerJac (rippleField ε) 0 (cylTorus (circR R₀ r) (circZ r)) θ φ =
      1 + ε * cos φ := by
    have hd : lineDeriv 0 (cylTorus (circR R₀ r) (circZ r)) θ φ = _ :=
      (hasDerivAt_circ_line hr hR θ φ).deriv
    rw [boozerJac, hd]
    simp only [cylTorus]
    rw [rippleField_cylPoint ε hρ, inner_smul_left, inner_smul_right,
      real_inner_self_eq_norm_sq, norm_toroidal_cylPoint hρ]
    simp only [conj_trivial]
    field_simp
  rw [torusQADefect, hL, hJ, boozerDeriv]
  unfold circR at hρ
  have := ripple_pos hε φ
  field_simp
  ring

/-- **Rejected fixture**: for `ε ≠ 0` the rippled field is not quasi-axisymmetric on the circular
torus: at `φ = π/2` the defect is `−ε/(R₀ + r cos θ) ≠ 0`. -/
theorem torusQADefect_ripple_ne_zero {ε R₀ r : ℝ} (hε : |ε| < 1) (hε0 : ε ≠ 0) (hr : 0 < r)
    (hR : r < R₀) (θ : ℝ) :
    torusQADefect (rippleField ε) 0 (cylTorus (circR R₀ r) (circZ r)) θ (π / 2) ≠ 0 := by
  rw [torusQADefect_ripple hε hr hR, sin_pi_div_two, cos_pi_div_two, mul_zero, add_zero,
    mul_one, mul_one]
  have := circR_pos hr hR θ 0
  unfold circR at this
  exact div_ne_zero (neg_ne_zero.2 hε0) this.ne'

/-- The rippled field violates every bound `TorusQADefectLe … δ` with `δ < |ε|/(R₀ + r)`. -/
theorem not_torusQADefectLe_ripple {ε R₀ r δ : ℝ} (hε : |ε| < 1) (hr : 0 < r) (hR : r < R₀)
    (hδ : δ < |ε| / (R₀ + r)) :
    ¬ TorusQADefectLe (rippleField ε) 0 (cylTorus (circR R₀ r) (circZ r)) δ := by
  intro h
  have h1 := h 0 (π / 2)
  rw [torusQADefect_ripple hε hr hR, sin_pi_div_two, cos_pi_div_two, cos_zero, mul_zero,
    add_zero, mul_one, mul_one, mul_one, abs_div, abs_neg, abs_of_pos (by linarith : 0 < R₀ + r)]
    at h1
  linarith

end Sanity

end PlasmaLean.Fields.VacuumBoozer
