/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Kernel.Vacuum
public import PlasmaLean.Theory.Fields.WeakQuasisymmetry
public import PlasmaLean.Theory.Fields.LieGradient

/-!
# Strong quasisymmetry of a fixed vacuum field as a linear system, and its jet obstruction

Source: the colleague's brief `gpt/stellarator_holomorphic_research_brief.pdf` (30 October 2026),
assessed in `notes/theory/holomorphic-qs-brief.md` (N-32); research question Q-25 (a).

Throughout, `B` is a vector field on Euclidean `ℝ³` (`Space`), `Q = |B|² = ⟪B, B⟫` (`fieldQ`).

## (a1) Strong QS as a linear system (FQS)

Strong quasisymmetry (SQS) with generator `u`, potential `Ψ` and constant `C` is
`ι_u β = dΨ` (`B × u = ∇Ψ`), `L_u α = 0` for `α = B♭` (as `dα = 0`, this is `d(B · u) = 0`;
we take `B · u = C` with a fixed constant `C`) and `L_u ν = 0` (`div u = 0`).
`StrongQSAt B u Ψ C x` states these three equations at the point `x`.

The fixed-field system (FQS) is `B · ∇Ψ = 0` and `(B × ∇Q) · ∇Ψ = -C B · ∇Q` (`FQSAt`).

* `cross_fqsVec`, `inner_fqsVec`, `eq_fqsVec_of_cross_of_inner`: pointwise algebra. If
  `B ≠ 0` and `B · ∇Ψ = 0`, then `u = (∇Ψ × B + C B)/Q` (`fqsGen`) solves `B × u = ∇Ψ`,
  `B · u = C`; conversely these two equations force this `u` and `B · ∇Ψ = 0`.
* `divergence_fqsGen_of_hasFDerivAt`: with explicit derivative data (`B` with derivative `DB`,
  `G` with derivative `DG`, both curl free, `div DB = 0`, `B x ≠ 0`) the field
  `(G × B + C B)/Q` has a derivative whose divergence is
  `-[Q'(G × B) + C Q'(B)]/Q²`, where `Q'(v) = 2⟪B, DB v⟫` is the derivative of `Q`.
* `fieldDiv_fqsGen`: the same for actual Fréchet derivatives, in the form of the brief:
  `div u = -[(B × ∇Q) · ∇Ψ + C B · ∇Q]/Q²`, for `B` differentiable at `x` with
  `curl B = div B = 0` at `x`, `B x ≠ 0` and `Ψ` of class `C²` at `x`.
* `fieldDiv_fqsGen_eq_zero_iff`: hence `div u = 0 ↔ (B × ∇Q) · ∇Ψ = -C B · ∇Q`.
* `StrongQSAt.fqsAt`: SQS on a neighbourhood of `x` (with the regularity above) implies FQS at
  `x`; `FQSAt.strongQSAt`: FQS at `x` implies SQS at `x` with generator `fqsGen B Ψ C`.

## (a2) The jet obstruction

`jet_obstruction` is stated for arbitrary fields `X`, `Y`, `Z`, `h`, `k` and a `C²` function `Ψ`
with, near `p`, `XΨ = 0`, `YΨ = -C h`, `Z = [X, Y]` and `k = X h` (Mathlib's
`VectorField.lieBracket`). Then also `ZΨ = -C k` near `p` (`fderiv_lieBracket_of_eventually`).
If `X(p)`, `Y(p)`, `Z(p)` are independent, `dΨ(p) = C η(p)` where `η(p) = w₀` solves
`⟪X, w₀⟫ = 0`, `⟪Y, w₀⟫ = -h`, `⟪Z, w₀⟫ = -k`; differentiating the three relations, the
Hessian of `Ψ` at `p` equals `C S` where `S` is the (unique) solution of the differentiated
linear system (`S = Dη(p)`, the Jacobian of `η`). Since the Hessian is symmetric,
`C (S - Sᵀ) = 0`. Consequences:

* `jet_obstruction_curl`: if `C ≠ 0` then `curl S = 0`, i.e. `dη(p) = 0`;
* `jet_obstruction_C_eq_zero`: if `curl S ≠ 0` then `C = 0`;
* `gradient_eventually_eq_zero_of_C_eq_zero`: if `C = 0` then `∇Ψ = 0` near `p`.

`jet_obstruction_eta` states the same with `η` the Cramer solution field (`cramer`) and `S` its
actual derivative at `p`: `C ≠ 0` forces `curl Dη(p) = 0`, i.e. `dη(p) = 0`.

`fqs_jet_obstruction` specialises to `X = B`, `Y = B × ∇Q`, `h = B · ∇Q` and FQS near `p`;
`strongQS_jet_obstruction` composes it with `StrongQSAt.fqsAt` for a vacuum field.

The dictionary with forms: `S` represents `Dη`, and `curl S` represents `dη` (its `z` component
`S e₀ · e₁ - S e₁ · e₀ = ∂ₓη_y - ∂_yη_x` is the `dx ∧ dy` coefficient). Concrete instance:
`PlasmaLean.Design.QSJetExample` (`B = ∇(xyz)` at `(1, 2, 3)`).

Scope: everything is local (a neighbourhood of one point of rank 3). Rank-deficient points and
global questions (solid tori, periods) are not treated.
-/

open scoped RealInnerProductSpace Topology
open InnerProductSpace Filter

public section
noncomputable section

namespace PlasmaLean.Fields.QSLinear
open PlasmaLean.Fields PlasmaLean.Vacuum

/-! ## Coordinates -/

/-- A vector from its three coordinates. -/
@[expose] def vec3 (a b c : ℝ) : Space := WithLp.toLp 2 ![a, b, c]

/-- First coordinate of `vec3`. -/
@[simp] theorem vec3_zero (a b c : ℝ) : vec3 a b c 0 = a := rfl

/-- Second coordinate of `vec3`. -/
@[simp] theorem vec3_one (a b c : ℝ) : vec3 a b c 1 = b := rfl

/-- Third coordinate of `vec3`. -/
@[simp] theorem vec3_two (a b c : ℝ) : vec3 a b c 2 = c := rfl

/-- First coordinate of a cross product. -/
@[simp] theorem cross_apply_zero (u v : Space) : cross u v 0 = u 1 * v 2 - u 2 * v 1 :=
  (cross_coords u v).1

/-- Second coordinate of a cross product. -/
@[simp] theorem cross_apply_one (u v : Space) : cross u v 1 = u 2 * v 0 - u 0 * v 2 :=
  (cross_coords u v).2.1

/-- Third coordinate of a cross product. -/
@[simp] theorem cross_apply_two (u v : Space) : cross u v 2 = u 0 * v 1 - u 1 * v 0 :=
  (cross_coords u v).2.2

/-- The inner product in coordinates. -/
theorem inner_coords (u v : Space) : ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three,
    star_trivial]
  ring

/-- `⟪b, b⟫ ≠ 0` for `b ≠ 0`. -/
theorem inner_self_ne_zero' {b : Space} (hb : b ≠ 0) : ⟪b, b⟫ ≠ 0 :=
  inner_self_ne_zero.mpr hb

/-- **Spanning by a nonzero triple product.** If `⟪a, b × c⟫ ≠ 0` and a linear functional
vanishes at `a`, `b`, `c`, it vanishes. -/
theorem clm_eq_zero_of_det {a b c : Space} (hdet : ⟪a, cross b c⟫ ≠ 0) (φ : Space →L[ℝ] ℝ)
    (ha : φ a = 0) (hb : φ b = 0) (hc : φ c = 0) : φ = 0 := by
  ext u
  have hu : ⟪a, cross b c⟫ • u =
      ⟪u, cross b c⟫ • a + ⟪u, cross c a⟫ • b + ⟪u, cross a b⟫ • c := by
    apply space_ext <;> simp [inner_coords] <;> ring
  have h := congrArg φ hu
  simp only [map_add, map_smul, ha, hb, hc, smul_eq_mul, mul_zero, add_zero] at h
  simpa [hdet] using h

/-- A vector orthogonal to an independent triple vanishes. -/
theorem eq_zero_of_inner_of_det {a b c v : Space} (hdet : ⟪a, cross b c⟫ ≠ 0)
    (ha : ⟪a, v⟫ = 0) (hb : ⟪b, v⟫ = 0) (hc : ⟪c, v⟫ = 0) : v = 0 := by
  have h := clm_eq_zero_of_det hdet (innerSL ℝ v)
    (by rw [innerSL_apply_apply, real_inner_comm, ha])
    (by rw [innerSL_apply_apply, real_inner_comm, hb])
    (by rw [innerSL_apply_apply, real_inner_comm, hc])
  have := congrArg (fun φ => φ v) h
  simpa using this

/-! ## (a1) Pointwise algebra -/

/-- `Q = |B|² = ⟪B, B⟫`. -/
@[expose] def fieldQ (B : Space → Space) (y : Space) : ℝ := ⟪B y, B y⟫

/-- `Q = ‖B‖²`. -/
theorem fieldQ_eq_norm_sq (B : Space → Space) (y : Space) : fieldQ B y = ‖B y‖ ^ 2 :=
  real_inner_self_eq_norm_sq _

/-- The pointwise generator `(g × b + C b)/|b|²`. -/
@[expose] def fqsVec (b g : Space) (C : ℝ) : Space := (⟪b, b⟫)⁻¹ • (cross g b + C • b)

/-- **The FQS generator** `u = (∇Ψ × B + C B)/Q`. -/
@[expose] def fqsGen (B : Space → Space) (Ψ : Space → ℝ) (C : ℝ) : Space → Space :=
  fun y => fqsVec (B y) (gradient Ψ y) C

/-- `b × (g × b + C b)/|b|² = g` when `b · g = 0`. -/
theorem cross_fqsVec {b g : Space} (C : ℝ) (hb : b ≠ 0) (hbg : ⟪b, g⟫ = 0) :
    cross b (fqsVec b g C) = g := by
  have hQ := inner_self_ne_zero' hb
  rw [inner_coords] at hbg
  have hq := inner_coords b b
  rw [fqsVec]
  generalize ⟪b, b⟫ = q at hQ hq
  apply space_ext <;> simp <;> field_simp
  · linear_combination (-(g 0)) * hq - b 0 * hbg
  · linear_combination (-(g 1)) * hq - b 1 * hbg
  · linear_combination (-(g 2)) * hq - b 2 * hbg

/-- `b · (g × b + C b)/|b|² = C`. -/
theorem inner_fqsVec {b g : Space} (C : ℝ) (hb : b ≠ 0) : ⟪b, fqsVec b g C⟫ = C := by
  have hQ := inner_self_ne_zero' hb
  rw [fqsVec, inner_smul_right, inner_add_right, inner_smul_right, inner_cross_right_self]
  field_simp
  ring

/-- **Converse.** `b × u = g` and `b · u = C` force `u = (g × b + C b)/|b|²` and `b · g = 0`. -/
theorem eq_fqsVec_of_cross_of_inner {b u g : Space} {C : ℝ} (hb : b ≠ 0)
    (hcross : cross b u = g) (hinner : ⟪b, u⟫ = C) : u = fqsVec b g C ∧ ⟪b, g⟫ = 0 := by
  refine ⟨?_, by rw [← hcross, inner_cross_left_self]⟩
  have hQ := inner_self_ne_zero' hb
  subst hcross hinner
  have hq := inner_coords b b
  rw [fqsVec, inner_coords b u]
  generalize ⟪b, b⟫ = q at hQ hq
  apply space_ext <;> simp <;> field_simp
  · linear_combination (u 0) * hq
  · linear_combination (u 1) * hq
  · linear_combination (u 2) * hq

/-! ## (a1) The divergence of the generator -/

/-- A linear map in coordinates: `(L v)ᵢ = ∑ⱼ vⱼ (L eⱼ)ᵢ`. -/
theorem clm_apply_coords (L : Space →L[ℝ] Space) (v : Space) (i : Fin 3) :
    L v i = v 0 * L (basis 0) i + v 1 * L (basis 1) i + v 2 * L (basis 2) i := by
  have hv : v = v 0 • basis 0 + v 1 • basis 1 + v 2 • basis 2 :=
    space_ext (by simp) (by simp) (by simp)
  conv_lhs => rw [hv]
  simp [map_add, map_smul]

/-- The kernel divergence agrees with `Fields.divergence`. -/
theorem divOp_eq_divergence (L : Space →L[ℝ] Space) : divOp L = divergence L := by
  rw [divOp_apply, divergence_apply]

/-- **Divergence of the FQS generator, explicit derivative data.** Let `B` have derivative `DB`
and `G` derivative `DG` at `x`, both curl free, `div DB = 0` and `B x ≠ 0`. Then
`y ↦ (G y × B y + C B y)/|B y|²` has a derivative `Du` at `x` with
`div Du = -[Q'(G × B) + C Q'(B)]/Q²`, where `Q'(v) = 2⟪B x, DB v⟫`. -/
theorem divergence_fqsGen_of_hasFDerivAt {B G : Space → Space} {DB DG : Space →L[ℝ] Space}
    {x : Space} (hB : HasFDerivAt B DB x) (hG : HasFDerivAt G DG x) (hBc : curlOp DB = 0)
    (hBd : divOp DB = 0) (hGc : curlOp DG = 0) (hne : B x ≠ 0) (C : ℝ) :
    ∃ Du : Space →L[ℝ] Space, HasFDerivAt (fun y => fqsVec (B y) (G y) C) Du x ∧
      divOp Du = -(2 * ⟪B x, DB (cross (G x) (B x))⟫ + C * (2 * ⟪B x, DB (B x)⟫)) /
        ⟪B x, B x⟫ ^ 2 := by
  have hQ0 := inner_self_ne_zero' hne
  have hQ := hB.inner ℝ hB
  have hI := (hasFDerivAt_inv hQ0).comp x hQ
  have hV := (crossBilinear.hasFDerivAt_of_bilinear hG hB).add (hB.const_smul C)
  have hU := hI.smul hV
  refine ⟨_, hU, ?_⟩
  rw [curlOp_eq_zero_iff] at hBc hGc
  rw [divOp_apply] at hBd ⊢
  have hq := inner_coords (B x) (B x)
  simp only [Function.comp_apply, add_apply, Pi.add_apply, Pi.smul_apply,
    ContinuousLinearMap.compL_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
    crossBilinear_apply, fderivInnerCLM_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.toSpanSingleton_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    cross_apply_zero, cross_apply_one, cross_apply_two, inner_coords]
  rw [clm_apply_coords DB (cross (G x) (B x)) 0, clm_apply_coords DB (cross (G x) (B x)) 1,
    clm_apply_coords DB (cross (G x) (B x)) 2, clm_apply_coords DB (B x) 0,
    clm_apply_coords DB (B x) 1, clm_apply_coords DB (B x) 2]
  simp only [cross_apply_zero, cross_apply_one, cross_apply_two]
  have hd : DB (basis 2) 2 = -(DB (basis 0) 0) - DB (basis 1) 1 := by linear_combination hBd
  rw [hBc 0 1, hBc 0 2, hBc 1 2, hGc 0 1, hGc 0 2, hGc 1 2, hd]
  field_simp
  ring

/-- A symmetric operator (`⟪L v, w⟫ = ⟪v, L w⟫`) is curl free. -/
theorem curlOp_eq_zero_of_symm (L : Space →L[ℝ] Space) (h : ∀ v w, ⟪L v, w⟫ = ⟪v, L w⟫) :
    curlOp L = 0 := by
  rw [curlOp_eq_zero_iff]
  intro i j
  have := h (basis j) (basis i)
  simp only [EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_left] at this
  simpa using this

/-- The Hessian of a `C²` function, as the derivative of its gradient, is curl free. -/
theorem curlOp_fderiv_gradient {Ψ : Space → ℝ} {x : Space} (hΨ : ContDiffAt ℝ 2 Ψ x) :
    curlOp (fderiv ℝ (gradient Ψ) x) = 0 := by
  have h := isSelfAdjoint_fderiv_gradient hΨ
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at h
  exact curlOp_eq_zero_of_symm _ fun v w => h v w

/-- The derivative of `Q = ⟪B, B⟫`: `⟪∇Q, v⟫ = 2⟪B, DB v⟫`. -/
theorem inner_gradient_fieldQ {B : Space → Space} {DB : Space →L[ℝ] Space} {x : Space}
    (hB : HasFDerivAt B DB x) (v : Space) :
    ⟪gradient (fieldQ B) x, v⟫ = 2 * ⟪B x, DB v⟫ := by
  have hQ : HasFDerivAt (fieldQ B) _ x := hB.inner ℝ hB
  rw [inner_gradient_left, hQ.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply]
  rw [real_inner_comm (DB v)]
  ring

/-- Triple product: `⟪b × q, g⟫ = ⟪q, g × b⟫`. -/
theorem inner_cross_cyclic (b q g : Space) : ⟪cross b q, g⟫ = ⟪q, cross g b⟫ := by
  simp only [inner_coords, cross_apply_zero, cross_apply_one, cross_apply_two]
  ring

/-- **Divergence of the FQS generator** (brief, eq. (FQS)). If `B` is differentiable at `x`
with `curl B = div B = 0` there, `B x ≠ 0` and `Ψ` is `C²` at `x`, then
`div u = -[(B × ∇Q) · ∇Ψ + C B · ∇Q]/Q²` for `u = (∇Ψ × B + C B)/Q`. -/
theorem fieldDiv_fqsGen {B : Space → Space} {Ψ : Space → ℝ} (C : ℝ) {x : Space}
    (hB : DifferentiableAt ℝ B x) (hΨ : ContDiffAt ℝ 2 Ψ x) (hcurl : fieldCurl B x = 0)
    (hdiv : fieldDiv B x = 0) (hne : B x ≠ 0) :
    fieldDiv (fqsGen B Ψ C) x =
      -(⟪cross (B x) (gradient (fieldQ B) x), gradient Ψ x⟫ +
        C * ⟪B x, gradient (fieldQ B) x⟫) / fieldQ B x ^ 2 := by
  obtain ⟨Du, hU, hdivU⟩ := divergence_fqsGen_of_hasFDerivAt hB.hasFDerivAt
    (hasFDerivAt_gradient hΨ) hcurl hdiv
    (by rw [← (hasFDerivAt_gradient hΨ).fderiv]; exact curlOp_fderiv_gradient hΨ) hne C
  have hfun : fqsGen B Ψ C = fun y => fqsVec (B y) (gradient Ψ y) C := rfl
  rw [fieldDiv, hfun, hU.fderiv, hdivU, inner_cross_cyclic,
    real_inner_comm (gradient (fieldQ B) x) (B x),
    inner_gradient_fieldQ hB.hasFDerivAt, inner_gradient_fieldQ hB.hasFDerivAt]
  rfl

/-- **(FQS) ⇔ `div u = 0`.** Under the hypotheses of `fieldDiv_fqsGen`,
`div u = 0 ↔ (B × ∇Q) · ∇Ψ = -C B · ∇Q`. -/
theorem fieldDiv_fqsGen_eq_zero_iff {B : Space → Space} {Ψ : Space → ℝ} (C : ℝ) {x : Space}
    (hB : DifferentiableAt ℝ B x) (hΨ : ContDiffAt ℝ 2 Ψ x) (hcurl : fieldCurl B x = 0)
    (hdiv : fieldDiv B x = 0) (hne : B x ≠ 0) :
    fieldDiv (fqsGen B Ψ C) x = 0 ↔
      ⟪cross (B x) (gradient (fieldQ B) x), gradient Ψ x⟫ =
        -C * ⟪B x, gradient (fieldQ B) x⟫ := by
  have hQ : fieldQ B x ^ 2 ≠ 0 := pow_ne_zero 2 (inner_self_ne_zero' hne)
  rw [fieldDiv_fqsGen C hB hΨ hcurl hdiv hne, div_eq_zero_iff, neg_eq_zero]
  constructor
  · rintro (h | h)
    · linear_combination h
    · exact absurd h hQ
  · intro h
    left
    linear_combination h

/-! ## (a1) Strong QS and the fixed-field system -/

/-- **Strong quasisymmetry at a point** (brief, §1): `B × u = ∇Ψ` (`ι_u β = dΨ`), `B · u = C`
(with `C` the same constant at every point considered, this is `L_u α = d(B · u) = 0` for the
closed form `α = B♭`), and `div u = 0` (`L_u ν = 0`). -/
structure StrongQSAt (B u : Space → Space) (Ψ : Space → ℝ) (C : ℝ) (x : Space) : Prop where
  /-- `B × u = ∇Ψ`. -/
  cross_eq : cross (B x) (u x) = gradient Ψ x
  /-- `B · u = C`. -/
  inner_eq : ⟪B x, u x⟫ = C
  /-- `div u = 0`. -/
  div_eq : fieldDiv u x = 0

/-- **The fixed-field system (FQS) at a point**: `B · ∇Ψ = 0` and
`(B × ∇Q) · ∇Ψ = -C B · ∇Q`, with `Q = |B|²`. -/
structure FQSAt (B : Space → Space) (Ψ : Space → ℝ) (C : ℝ) (x : Space) : Prop where
  /-- `B · ∇Ψ = 0`. -/
  inner_eq : ⟪B x, gradient Ψ x⟫ = 0
  /-- `(B × ∇Q) · ∇Ψ = -C B · ∇Q`. -/
  moment_eq : ⟪cross (B x) (gradient (fieldQ B) x), gradient Ψ x⟫ =
    -C * ⟪B x, gradient (fieldQ B) x⟫

/-- **SQS ⇒ FQS.** If SQS holds on a neighbourhood of `x` (only `B × u = ∇Ψ` and `B · u = C`
are used off `x`), `B` is differentiable at `x` with `curl B = div B = 0` there, `B x ≠ 0`
and `Ψ` is `C²` at `x`, then FQS holds at `x`. (No regularity of `u` is assumed: near `x`,
`u` coincides with `fqsGen B Ψ C`.) -/
theorem StrongQSAt.fqsAt {B u : Space → Space} {Ψ : Space → ℝ} {C : ℝ} {x : Space}
    (h : ∀ᶠ y in 𝓝 x, StrongQSAt B u Ψ C y) (hB : DifferentiableAt ℝ B x)
    (hΨ : ContDiffAt ℝ 2 Ψ x) (hcurl : fieldCurl B x = 0) (hdiv : fieldDiv B x = 0)
    (hne : B x ≠ 0) : FQSAt B Ψ C x := by
  have hne' : ∀ᶠ y in 𝓝 x, B y ≠ 0 := hB.continuousAt.eventually_ne hne
  have heq : u =ᶠ[𝓝 x] fqsGen B Ψ C := by
    filter_upwards [h, hne'] with y hy hb
    exact (eq_fqsVec_of_cross_of_inner hb hy.cross_eq hy.inner_eq).1
  have hx := h.self_of_nhds
  refine ⟨(eq_fqsVec_of_cross_of_inner hne hx.cross_eq hx.inner_eq).2, ?_⟩
  rw [← fieldDiv_fqsGen_eq_zero_iff C hB hΨ hcurl hdiv hne, ← hx.div_eq]
  simp only [fieldDiv, heq.fderiv_eq]

/-- **FQS ⇒ SQS.** Under the same regularity, FQS at `x` gives SQS at `x` with the generator
`u = (∇Ψ × B + C B)/Q`. -/
theorem FQSAt.strongQSAt {B : Space → Space} {Ψ : Space → ℝ} {C : ℝ} {x : Space}
    (h : FQSAt B Ψ C x) (hB : DifferentiableAt ℝ B x) (hΨ : ContDiffAt ℝ 2 Ψ x)
    (hcurl : fieldCurl B x = 0) (hdiv : fieldDiv B x = 0) (hne : B x ≠ 0) :
    StrongQSAt B (fqsGen B Ψ C) Ψ C x :=
  ⟨cross_fqsVec C hne h.inner_eq, inner_fqsVec C hne,
    (fieldDiv_fqsGen_eq_zero_iff C hB hΨ hcurl hdiv hne).mpr h.moment_eq⟩

/-- **SQS on a neighbourhood gives FQS on a neighbourhood**, for a vacuum field. -/
theorem eventually_fqsAt_of_strongQS {Ω : Set Space} {B u : Space → Space} {Ψ : Space → ℝ}
    {C : ℝ} {p : Space} {U : Set Space} (hvac : VacuumField Ω B) (hp : p ∈ Ω)
    (hΨ : ContDiffAt ℝ 2 Ψ p) (hne : B p ≠ 0) (hU : U ∈ 𝓝 p)
    (h : ∀ y ∈ U, StrongQSAt B u Ψ C y) : ∀ᶠ y in 𝓝 p, FQSAt B Ψ C y := by
  have hΩ : Ω ∈ 𝓝 p := hvac.isOpen.mem_nhds hp
  have hBd : ∀ y ∈ Ω, DifferentiableAt ℝ B y := fun y hy =>
    ((hvac.contDiffOn y hy).contDiffAt (hvac.isOpen.mem_nhds hy)).differentiableAt
      (by norm_num)
  have hne' : ∀ᶠ y in 𝓝 p, B y ≠ 0 := (hBd p hp).continuousAt.eventually_ne hne
  filter_upwards [hΩ, hΨ.eventually (by simp), hne', eventually_eventually_nhds.mpr hU]
    with y hyΩ hΨy hny hUy
  exact StrongQSAt.fqsAt (hUy.mono h) (hBd y hyΩ) hΨy (hvac.curl_eq_zero y hyΩ)
    (hvac.div_eq_zero y hyΩ) hny

/-! ## (a2) The jet obstruction -/

/-- The derivative of `z ↦ DΨ(z)(V z)` for `Ψ` of class `C²`:
`v ↦ DΨ(y)(DV v) + D²Ψ(y) v (V y)`. -/
theorem hasFDerivAt_fderiv_apply {Ψ : Space → ℝ} {V : Space → Space}
    {DV : Space →L[ℝ] Space} {y : Space} (hΨ : ContDiffAt ℝ 2 Ψ y) (hV : HasFDerivAt V DV y) :
    HasFDerivAt (fun z => fderiv ℝ Ψ z (V z))
      ((fderiv ℝ Ψ y).comp DV + (fderiv ℝ (fderiv ℝ Ψ) y).flip (V y)) y := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ Ψ) y :=
    (hΨ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact hdf.hasFDerivAt.clm_apply hV

/-- Differentiating a relation `DΨ(z)(V z) = f z` that holds near `y`. -/
theorem fderiv_apply_relation {Ψ f : Space → ℝ} {V : Space → Space} {DV : Space →L[ℝ] Space}
    {f' : Space →L[ℝ] ℝ} {y : Space} (hΨ : ContDiffAt ℝ 2 Ψ y) (hV : HasFDerivAt V DV y)
    (hf : HasFDerivAt f f' y) (heq : ∀ᶠ z in 𝓝 y, fderiv ℝ Ψ z (V z) = f z) (v : Space) :
    fderiv ℝ Ψ y (DV v) + fderiv ℝ (fderiv ℝ Ψ) y v (V y) = f' v := by
  have h := (hasFDerivAt_fderiv_apply hΨ hV).unique (hf.congr_of_eventuallyEq heq)
  rw [← h]
  simp

/-- **The bracket relation.** If `XΨ = 0` and `YΨ = -C h` near `y`, `Ψ` is `C²` at `y` and
`X`, `Y`, `h` are differentiable at `y`, then `[X, Y]Ψ = -C (X h)` at `y`. -/
theorem fderiv_lieBracket_of_eventually {X Y : Space → Space} {h Ψ : Space → ℝ} {C : ℝ}
    {y : Space} (hΨ : ContDiffAt ℝ 2 Ψ y) (hX : DifferentiableAt ℝ X y)
    (hY : DifferentiableAt ℝ Y y) (hh : DifferentiableAt ℝ h y)
    (h1 : ∀ᶠ z in 𝓝 y, fderiv ℝ Ψ z (X z) = 0)
    (h2 : ∀ᶠ z in 𝓝 y, fderiv ℝ Ψ z (Y z) = -C * h z) :
    fderiv ℝ Ψ y (VectorField.lieBracket ℝ X Y y) = -C * fderiv ℝ h y (X y) := by
  have r1 := fderiv_apply_relation hΨ hX.hasFDerivAt (hasFDerivAt_const 0 y) h1 (Y y)
  have r2 := fderiv_apply_relation hΨ hY.hasFDerivAt (hh.hasFDerivAt.const_mul (-C)) h2 (X y)
  have hs := hΨ.isSymmSndFDerivAt (by simp) (X y) (Y y)
  simp only [zero_apply, smul_apply,
    smul_eq_mul] at r1 r2
  rw [VectorField.lieBracket, map_sub]
  linear_combination r2 - r1 - hs

/-- **Hypotheses of the jet obstruction** at `p`, for fields `X`, `Y`, `Z`, functions `h`, `k`
and a potential `Ψ`, with the derivatives `DX`, `DY`, `DZ`, `Dh`, `Dk` at `p`:
`Ψ` is `C²` at `p`; `X`, `Y`, `h` are differentiable near `p`; `Z = [X, Y]` and `k = X h` near
`p`; the FQS relations `XΨ = 0` and `YΨ = -C h` hold near `p`; and `X(p)`, `Y(p)`, `Z(p)` are
linearly independent. -/
structure JetHyp (X Y Z : Space → Space) (h k Ψ : Space → ℝ) (C : ℝ) (p : Space)
    (DX DY DZ : Space →L[ℝ] Space) (Dh Dk : Space →L[ℝ] ℝ) : Prop where
  /-- `Ψ` is `C²` at `p`. -/
  psi : ContDiffAt ℝ 2 Ψ p
  /-- `X` is differentiable near `p`. -/
  X_diff : ∀ᶠ y in 𝓝 p, DifferentiableAt ℝ X y
  /-- `Y` is differentiable near `p`. -/
  Y_diff : ∀ᶠ y in 𝓝 p, DifferentiableAt ℝ Y y
  /-- `h` is differentiable near `p`. -/
  h_diff : ∀ᶠ y in 𝓝 p, DifferentiableAt ℝ h y
  /-- Derivative of `X` at `p`. -/
  X_deriv : HasFDerivAt X DX p
  /-- Derivative of `Y` at `p`. -/
  Y_deriv : HasFDerivAt Y DY p
  /-- Derivative of `Z` at `p`. -/
  Z_deriv : HasFDerivAt Z DZ p
  /-- Derivative of `h` at `p`. -/
  h_deriv : HasFDerivAt h Dh p
  /-- Derivative of `k` at `p`. -/
  k_deriv : HasFDerivAt k Dk p
  /-- `Z = [X, Y]` near `p`. -/
  Z_eq : ∀ᶠ y in 𝓝 p, Z y = VectorField.lieBracket ℝ X Y y
  /-- `k = X h` near `p`. -/
  k_eq : ∀ᶠ y in 𝓝 p, k y = fderiv ℝ h y (X y)
  /-- `XΨ = 0` near `p`. -/
  rel_X : ∀ᶠ y in 𝓝 p, fderiv ℝ Ψ y (X y) = 0
  /-- `YΨ = -C h` near `p`. -/
  rel_Y : ∀ᶠ y in 𝓝 p, fderiv ℝ Ψ y (Y y) = -C * h y
  /-- `X(p)`, `Y(p)`, `Z(p)` are independent. -/
  det_ne : ⟪X p, cross (Y p) (Z p)⟫ ≠ 0

/-- **The linear data of the obstruction**: `w₀ = η(p)` solves `⟪X, w₀⟫ = 0`, `⟪Y, w₀⟫ = -h`,
`⟪Z, w₀⟫ = -k` at `p`, and `S` (playing the role of `Dη(p)`) solves the differentiated system
`⟪X, S v⟫ = -⟪DX v, w₀⟫`, `⟪Y, S v⟫ = -Dh v - ⟪DY v, w₀⟫`, `⟪Z, S v⟫ = -Dk v - ⟪DZ v, w₀⟫`. -/
structure JetSolution (X Y Z : Space → Space) (h k : Space → ℝ) (p : Space)
    (DX DY DZ : Space →L[ℝ] Space) (Dh Dk : Space →L[ℝ] ℝ) (w₀ : Space)
    (S : Space →L[ℝ] Space) : Prop where
  /-- `⟪X(p), w₀⟫ = 0`. -/
  w_X : ⟪X p, w₀⟫ = 0
  /-- `⟪Y(p), w₀⟫ = -h(p)`. -/
  w_Y : ⟪Y p, w₀⟫ = -h p
  /-- `⟪Z(p), w₀⟫ = -k(p)`. -/
  w_Z : ⟪Z p, w₀⟫ = -k p
  /-- First differentiated equation. -/
  S_X : ∀ v, ⟪X p, S v⟫ = -⟪DX v, w₀⟫
  /-- Second differentiated equation. -/
  S_Y : ∀ v, ⟪Y p, S v⟫ = -Dh v - ⟪DY v, w₀⟫
  /-- Third differentiated equation. -/
  S_Z : ∀ v, ⟪Z p, S v⟫ = -Dk v - ⟪DZ v, w₀⟫

namespace JetHyp

variable {X Y Z : Space → Space} {h k Ψ : Space → ℝ} {C : ℝ} {p : Space}
  {DX DY DZ : Space →L[ℝ] Space} {Dh Dk : Space →L[ℝ] ℝ}

/-- `ZΨ = -C k` near `p` (from `[X, Y]Ψ = X(YΨ) - Y(XΨ)`). -/
theorem rel_Z (H : JetHyp X Y Z h k Ψ C p DX DY DZ Dh Dk) :
    ∀ᶠ y in 𝓝 p, fderiv ℝ Ψ y (Z y) = -C * k y := by
  filter_upwards [H.psi.eventually (by simp), H.X_diff, H.Y_diff, H.h_diff,
    eventually_eventually_nhds.mpr H.rel_X, eventually_eventually_nhds.mpr H.rel_Y, H.Z_eq,
    H.k_eq] with y hΨy hXy hYy hhy h1y h2y hZy hky
  rw [hZy, hky]
  exact fderiv_lieBracket_of_eventually hΨy hXy hYy hhy h1y h2y

/-- `X`, `Y`, `Z` stay independent near `p`. -/
theorem det_eventually_ne (H : JetHyp X Y Z h k Ψ C p DX DY DZ Dh Dk) :
    ∀ᶠ y in 𝓝 p, ⟪X y, cross (Y y) (Z y)⟫ ≠ 0 := by
  have hc : ContinuousAt (fun y => cross (Y y) (Z y)) p :=
    continuous_cross.continuousAt.comp (f := fun y => (Y y, Z y))
      (H.Y_deriv.continuousAt.prodMk H.Z_deriv.continuousAt)
  exact (H.X_deriv.continuousAt.inner hc).eventually_ne H.det_ne

/-- **The jet obstruction** (brief, §2). Under `JetHyp` and with the linear data `JetSolution`,
the Hessian of `Ψ` at `p` is `C S`; since it is symmetric, `C ⟪S v, u⟫ = C ⟪S u, v⟫`. -/
theorem jet_obstruction (H : JetHyp X Y Z h k Ψ C p DX DY DZ Dh Dk) {w₀ : Space}
    {S : Space →L[ℝ] Space} (hS : JetSolution X Y Z h k p DX DY DZ Dh Dk w₀ S) (u v : Space) :
    C * ⟪S v, u⟫ = C * ⟪S u, v⟫ := by
  have h3 := H.rel_Z
  have hdΨ : fderiv ℝ Ψ p = C • innerSL ℝ w₀ := by
    refine sub_eq_zero.mp (clm_eq_zero_of_det H.det_ne _ ?_ ?_ ?_) <;>
      simp only [sub_apply, smul_apply,
        innerSL_apply_apply, smul_eq_mul]
    · rw [H.rel_X.self_of_nhds, real_inner_comm, hS.w_X]; ring
    · rw [H.rel_Y.self_of_nhds, real_inner_comm, hS.w_Y]; ring
    · rw [h3.self_of_nhds, real_inner_comm, hS.w_Z]; ring
  have hD2 : ∀ v, fderiv ℝ (fderiv ℝ Ψ) p v = C • innerSL ℝ (S v) := by
    intro v
    have r1 := fderiv_apply_relation H.psi H.X_deriv (hasFDerivAt_const 0 p) H.rel_X v
    have r2 := fderiv_apply_relation H.psi H.Y_deriv (H.h_deriv.const_mul (-C)) H.rel_Y v
    have r3 := fderiv_apply_relation H.psi H.Z_deriv (H.k_deriv.const_mul (-C)) h3 v
    rw [hdΨ] at r1 r2 r3
    simp only [zero_apply, smul_apply,
      innerSL_apply_apply, smul_eq_mul] at r1 r2 r3
    have s1 := hS.S_X v
    have s2 := hS.S_Y v
    have s3 := hS.S_Z v
    rw [real_inner_comm w₀ (DX v)] at s1
    rw [real_inner_comm w₀ (DY v)] at s2
    rw [real_inner_comm w₀ (DZ v)] at s3
    refine sub_eq_zero.mp (clm_eq_zero_of_det H.det_ne _ ?_ ?_ ?_) <;>
      simp only [sub_apply, smul_apply,
        innerSL_apply_apply, smul_eq_mul]
    · rw [real_inner_comm (X p) (S v)]; linear_combination r1 - C * s1
    · rw [real_inner_comm (Y p) (S v)]; linear_combination r2 - C * s2
    · rw [real_inner_comm (Z p) (S v)]; linear_combination r3 - C * s3
  have hs := H.psi.isSymmSndFDerivAt (by simp) v u
  rw [hD2, hD2] at hs
  simpa using hs

/-- **`C ≠ 0` forces `dη(p) = 0`**: the solution `S` of the differentiated system is curl
free. -/
theorem jet_obstruction_curl (H : JetHyp X Y Z h k Ψ C p DX DY DZ Dh Dk) {w₀ : Space}
    {S : Space →L[ℝ] Space} (hS : JetSolution X Y Z h k p DX DY DZ Dh Dk w₀ S) (hC : C ≠ 0) :
    curlOp S = 0 :=
  curlOp_eq_zero_of_symm S fun v w => by
    rw [real_inner_comm (S w) v]
    exact mul_left_cancel₀ hC (H.jet_obstruction hS w v)

/-- **Contrapositive: `dη(p) ≠ 0` forces `C = 0`.** -/
theorem jet_obstruction_C_eq_zero (H : JetHyp X Y Z h k Ψ C p DX DY DZ Dh Dk) {w₀ : Space}
    {S : Space →L[ℝ] Space} (hS : JetSolution X Y Z h k p DX DY DZ Dh Dk w₀ S)
    (hcurl : curlOp S ≠ 0) : C = 0 := by
  by_contra hC
  exact hcurl (H.jet_obstruction_curl hS hC)

/-- **`C = 0` forces `∇Ψ = 0` near `p`** (no regular level sets of `Ψ`). -/
theorem gradient_eventually_eq_zero (H : JetHyp X Y Z h k Ψ C p DX DY DZ Dh Dk) (hC : C = 0) :
    ∀ᶠ y in 𝓝 p, gradient Ψ y = 0 := by
  filter_upwards [H.det_eventually_ne, H.rel_X, H.rel_Y, H.rel_Z] with y hd h1 h2 h3
  subst hC
  refine eq_zero_of_inner_of_det hd ?_ ?_ ?_ <;>
    rw [real_inner_comm, inner_gradient_left] <;> simp [h1, h2, h3]

end JetHyp

/-! ## (a2) The Cramer form of `η` -/

/-- **Cramer's rule**: the solution of `⟪a, w⟫ = α`, `⟪b, w⟫ = β`, `⟪c, w⟫ = γ`. -/
@[expose] def cramer (a b c : Space) (α β γ : ℝ) : Space :=
  (⟪a, cross b c⟫)⁻¹ • (α • cross b c + β • cross c a + γ • cross a b)

/-- `cramer` solves the system when `⟪a, b × c⟫ ≠ 0`. -/
theorem cramer_spec {a b c : Space} (α β γ : ℝ) (hdet : ⟪a, cross b c⟫ ≠ 0) :
    ⟪a, cramer a b c α β γ⟫ = α ∧ ⟪b, cramer a b c α β γ⟫ = β ∧
      ⟪c, cramer a b c α β γ⟫ = γ := by
  have e1 : ⟪b, cross c a⟫ = ⟪a, cross b c⟫ := by
    simp only [inner_coords, cross_apply_zero, cross_apply_one, cross_apply_two]; ring
  have e2 : ⟪c, cross a b⟫ = ⟪a, cross b c⟫ := by
    simp only [inner_coords, cross_apply_zero, cross_apply_one, cross_apply_two]; ring
  have z1 : ⟪b, cross b c⟫ = 0 := inner_cross_left_self b c
  have z2 : ⟪c, cross b c⟫ = 0 := inner_cross_right_self b c
  have z3 : ⟪a, cross c a⟫ = 0 := inner_cross_right_self c a
  have z4 : ⟪c, cross c a⟫ = 0 := inner_cross_left_self c a
  have z5 : ⟪a, cross a b⟫ = 0 := inner_cross_left_self a b
  have z6 : ⟪b, cross a b⟫ = 0 := inner_cross_right_self a b
  simp only [cramer, inner_smul_right, inner_add_right, e1, e2, z1, z2, z3, z4, z5, z6]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- The one-form `η` of the brief, as a vector field: `η(X) = 0`, `η(Y) = -h`, `η(Z) = -k`. -/
@[expose] def jetEta (X Y Z : Space → Space) (h k : Space → ℝ) : Space → Space :=
  fun y => cramer (X y) (Y y) (Z y) 0 (-h y) (-k y)

/-- Differentiating a relation `⟪A z, η z⟫ = f z` that holds near `p`. -/
theorem inner_deriv_relation {A η : Space → Space} {DA Dη : Space →L[ℝ] Space}
    {f : Space → ℝ} {f' : Space →L[ℝ] ℝ} {p : Space} (hA : HasFDerivAt A DA p)
    (hη : HasFDerivAt η Dη p) (hf : HasFDerivAt f f' p)
    (heq : ∀ᶠ z in 𝓝 p, ⟪A z, η z⟫ = f z) (v : Space) :
    ⟪DA v, η p⟫ + ⟪A p, Dη v⟫ = f' v := by
  have h := (hA.inner ℝ hη).unique (hf.congr_of_eventuallyEq heq)
  rw [← h]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply]
  ring

/-- **The jet obstruction for the Cramer one-form.** Under `JetHyp`, if `η = jetEta X Y Z h k`
has derivative `Dη` at `p` and `C ≠ 0`, then `curl Dη(p) = 0`, i.e. `dη(p) = 0`. -/
theorem jet_obstruction_eta {X Y Z : Space → Space} {h k Ψ : Space → ℝ} {C : ℝ} {p : Space}
    {DX DY DZ : Space →L[ℝ] Space} {Dh Dk : Space →L[ℝ] ℝ}
    (H : JetHyp X Y Z h k Ψ C p DX DY DZ Dh Dk) {Dη : Space →L[ℝ] Space}
    (hη : HasFDerivAt (jetEta X Y Z h k) Dη p) (hC : C ≠ 0) : curlOp Dη = 0 := by
  have hsol : ∀ᶠ y in 𝓝 p, ⟪X y, jetEta X Y Z h k y⟫ = 0 ∧
      ⟪Y y, jetEta X Y Z h k y⟫ = -h y ∧ ⟪Z y, jetEta X Y Z h k y⟫ = -k y := by
    filter_upwards [H.det_eventually_ne] with y hy
    exact cramer_spec _ _ _ hy
  obtain ⟨w1, w2, w3⟩ := hsol.self_of_nhds
  refine H.jet_obstruction_curl (w₀ := jetEta X Y Z h k p) ⟨w1, w2, w3, fun v => ?_,
    fun v => ?_, fun v => ?_⟩ hC
  · have := inner_deriv_relation H.X_deriv hη (hasFDerivAt_const 0 p)
      (hsol.mono fun y hy => hy.1) v
    simp only [zero_apply] at this
    linear_combination this
  · have := inner_deriv_relation H.Y_deriv hη H.h_deriv.neg (hsol.mono fun y hy => hy.2.1) v
    simp only [neg_apply] at this
    linear_combination this
  · have := inner_deriv_relation H.Z_deriv hη H.k_deriv.neg (hsol.mono fun y hy => hy.2.2) v
    simp only [neg_apply] at this
    linear_combination this

/-! ## (a2) Specialisation to the fixed-field system -/

/-- The second field of the brief, `Y = B × ∇Q`. -/
@[expose] def fieldY (B : Space → Space) : Space → Space :=
  fun y => cross (B y) (gradient (fieldQ B) y)

/-- The function `h = B · ∇Q`. -/
@[expose] def fieldH (B : Space → Space) : Space → ℝ := fun y => ⟪B y, gradient (fieldQ B) y⟫

/-- FQS gives the first relation `BΨ = 0`. -/
theorem FQSAt.rel_X {B : Space → Space} {Ψ : Space → ℝ} {C : ℝ} {y : Space}
    (h : FQSAt B Ψ C y) : fderiv ℝ Ψ y (B y) = 0 := by
  rw [← inner_gradient_left, real_inner_comm, h.inner_eq]

/-- FQS gives the second relation `YΨ = -C h`. -/
theorem FQSAt.rel_Y {B : Space → Space} {Ψ : Space → ℝ} {C : ℝ} {y : Space}
    (h : FQSAt B Ψ C y) : fderiv ℝ Ψ y (fieldY B y) = -C * fieldH B y := by
  rw [← inner_gradient_left, real_inner_comm, fieldY, fieldH, h.moment_eq]

/-- **Jet obstruction for strong QS of a vacuum field.** Let `B` be a vacuum field on `Ω ∋ p`
with `B p ≠ 0`, and suppose SQS (`StrongQSAt B u Ψ C`) holds on a neighbourhood `U` of `p` with
`Ψ` of class `C²` at `p`. Let `X = B`, `Y = B × ∇Q`, `h = B · ∇Q`, `Z`, `k` with the regularity
of `JetHyp` (`Z = [X, Y]`, `k = X h` near `p`, `X(p)`, `Y(p)`, `Z(p)` independent), and let
`(w₀, S)` solve the linear system at `p`. If `curl S ≠ 0` (i.e. `dη(p) ≠ 0`), then `C = 0` and
`∇Ψ = 0` near `p`. -/
theorem strongQS_jet_obstruction {Ω : Set Space} {B u Z : Space → Space} {k Ψ : Space → ℝ}
    {C : ℝ} {p : Space} {U : Set Space} {DX DY DZ : Space →L[ℝ] Space}
    {Dh Dk : Space →L[ℝ] ℝ} {w₀ : Space} {S : Space →L[ℝ] Space}
    (hvac : VacuumField Ω B) (hp : p ∈ Ω) (hne : B p ≠ 0) (hU : U ∈ 𝓝 p)
    (hΨ : ContDiffAt ℝ 2 Ψ p) (hSQS : ∀ y ∈ U, StrongQSAt B u Ψ C y)
    (hXd : ∀ᶠ y in 𝓝 p, DifferentiableAt ℝ B y)
    (hYd : ∀ᶠ y in 𝓝 p, DifferentiableAt ℝ (fieldY B) y)
    (hhd : ∀ᶠ y in 𝓝 p, DifferentiableAt ℝ (fieldH B) y)
    (hX : HasFDerivAt B DX p) (hY : HasFDerivAt (fieldY B) DY p) (hZ : HasFDerivAt Z DZ p)
    (hh : HasFDerivAt (fieldH B) Dh p) (hk : HasFDerivAt k Dk p)
    (hZeq : ∀ᶠ y in 𝓝 p, Z y = VectorField.lieBracket ℝ B (fieldY B) y)
    (hkeq : ∀ᶠ y in 𝓝 p, k y = fderiv ℝ (fieldH B) y (B y))
    (hdet : ⟪B p, cross (fieldY B p) (Z p)⟫ ≠ 0)
    (hS : JetSolution B (fieldY B) Z (fieldH B) k p DX DY DZ Dh Dk w₀ S)
    (hcurl : curlOp S ≠ 0) :
    C = 0 ∧ ∀ᶠ y in 𝓝 p, gradient Ψ y = 0 := by
  have hF := eventually_fqsAt_of_strongQS hvac hp hΨ hne hU hSQS
  have H : JetHyp B (fieldY B) Z (fieldH B) k Ψ C p DX DY DZ Dh Dk :=
    ⟨hΨ, hXd, hYd, hhd, hX, hY, hZ, hh, hk, hZeq, hkeq, hF.mono fun y hy => hy.rel_X,
      hF.mono fun y hy => hy.rel_Y, hdet⟩
  have hC := H.jet_obstruction_C_eq_zero hS hcurl
  exact ⟨hC, H.gradient_eventually_eq_zero hC⟩

/-! ## Sanity checks -/

/-- Degenerate case: a uniform field with constant potential satisfies FQS for every `C`
(`∇Q = 0` and `∇Ψ = 0`). -/
theorem fqsAt_uniform (C : ℝ) (x : Space) : FQSAt (fun _ => basis 2) (fun _ => 0) C x := by
  have hQ : gradient (fieldQ fun _ : Space => basis 2) x = 0 := by
    exact gradient_fun_const x _
  refine ⟨?_, ?_⟩ <;> simp [hQ, gradient_fun_const]

/-- Accepted fixture: Cramer's rule on the standard basis returns the right-hand side. -/
theorem cramer_basis (α β γ : ℝ) : cramer (basis 0) (basis 1) (basis 2) α β γ = vec3 α β γ := by
  apply space_ext <;> simp [cramer, inner_coords]

/-- Rejected fixture: without `b · g = 0` the generator formula fails, e.g.
`e_z × (e_z × e_z + 0 e_z)/1 = 0 ≠ e_z`. -/
theorem cross_fqsVec_fails : cross (basis 2) (fqsVec (basis 2) (basis 2) 0) ≠ basis 2 := by
  intro h
  have := congrArg (fun v : Space => v 2) h
  simp [fqsVec] at this

end PlasmaLean.Fields.QSLinear
