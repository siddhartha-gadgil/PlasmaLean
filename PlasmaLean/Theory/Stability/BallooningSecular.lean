/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Stability.BallooningSurface

/-!
# The secular drive is a parallel-current derivative: `B · ∇(J·B/|B|²) = 2μ ⟪B × ∇ψ, κ⟫/|B|²`

In the surface form of the SUPPLIED ballooning reduction (`BallooningSurface`), the drive on
the eikonal family is `Q = q₀ + s q₁` with the geodesic (secular) part
`q₁ = −2μ ⟪B × ∇ψ, κ⟫/|B|²` (`μ₀∇p = μ ∇ψ`). A surface certificate `Φ(x, s)` must satisfy
`DΦ(B, d) + Φ²/P ≤ Q` for ALL `s ∈ ℝ`; as `s → ±∞` this forces `Φ = a s + O(1)` with the
magnetic differential equation `B · ∇a = q₁` solved EXACTLY. This module proves that the
parallel current gives the exact solution, for a general three-dimensional equilibrium:

* `secular_algebra` (pointwise algebra): with `M = DB` trace free, `M₂ = D²B` symmetric,
  `H = D(∇ψ)` symmetric, the force balance `M B − Mᵀ B = μ ∇ψ` and its derivative,
  `(⟪curl (M₂ B), B⟫ + ⟪curl M, M B⟫)/|B|² − ⟪curl M, B⟫ 2⟪B, M B⟫/|B|⁴ = 2μ ⟪B × ∇ψ, κ⟫/|B|²`.
  Only the symmetry of the second derivatives and `tr M = 0` are used (the identity holds up to
  `−tr M |B|² ⟪curl M, B⟫`); `inner_curl_dir` is the contraction of the differentiated force
  balance.
* `jparOf`, `jparDeriv`, `hasFDerivAt_jpar`: `J∥ = ⟪curl M, B⟫/|B|²` and its Fréchet
  derivative; `force_balance_deriv`: differentiating `M B − Mᵀ B = μ g` on a neighbourhood;
  `hasFDerivAt_grad_symm`: a `C²` gradient has a coordinate-symmetric derivative.
* `jpar_transport`: **`B · ∇J∥ = 2μ ⟪B × ∇ψ, κ⟫/|B|² = −q₁`** at every point where `B` is
  `C²`, `∇ · B = 0`, `B ≠ 0` and the force balance holds nearby.
* `eikLine_stable_of_secularCert`: the surface certificate theorem with
  `Φ = (c₀ − j) s + F(x, s)`: if `B · ∇j = −q₁`, stability of every eikonal family of a line
  follows from the `q₁`-free inequality `DF(B, d) + d (c₀ − j) + ((c₀ − j)s + F)²/P ≤ q₀`.

Sanity: `jparOf_zero` (degenerate), `jparOf_rotation` (rigid rotation, `curl = 2ω`),
`eikLine_secular_noDrive_stable` (no pressure: the trivial certificate works).
-/

open scoped RealInnerProductSpace

public section
noncomputable section

namespace PlasmaLean.Stability.BallooningSecular

open Set Filter Topology WithLp
open PlasmaLean.Fields PlasmaLean.Stability PlasmaLean.Stability.BallooningReduction
open PlasmaLean.Stability.BallooningSurface

/-! ## The algebraic core -/

/-- The curl of a derivative operator contracted with `B`, in coordinates. -/
theorem inner_curl_coords (L : Space →L[ℝ] Space) (B : Space) :
    ⟪curl L, B⟫ = (L (basis 1) 2 - L (basis 2) 1) * B 0 + (L (basis 2) 0 - L (basis 0) 2) * B 1 +
      (L (basis 0) 1 - L (basis 1) 0) * B 2 := by
  obtain ⟨h0, h1, h2⟩ := curl_coords L
  rw [inner_coords, h0, h1, h2]

/-- **Contraction of the differentiated force balance.** If `T = M₂ B` with `M₂` symmetric
(`M₂ u v = M₂ v u`, a second derivative), `H` symmetric, and the derivative of the force
balance `M B − Mᵀ B = μ g` holds in every direction,
`M₂ v B + M (M v) − (M₂ v)ᵀ B − Mᵀ (M v) = μ H v`, then
`⟪curl (M₂ B), B⟫ = Σ ε_{ipq} B_i (M M e_q)_p`: all the symmetric terms drop out. -/
theorem inner_curl_dir (M : Space →L[ℝ] Space) (M₂ : Space →L[ℝ] Space →L[ℝ] Space)
    (H : Space →L[ℝ] Space) (B : Space) (μ : ℝ) (hsym : ∀ u v, M₂ u v = M₂ v u)
    (hH : CoordSymm H)
    (hE : ∀ v, M₂ v B + M (M v) - tApply (M₂ v) B - tApply M (M v) = μ • H v) :
    ⟪curl (M₂ B), B⟫ =
      (M (M (basis 2)) 1 - M (M (basis 1)) 2) * B 0 +
      (M (M (basis 0)) 2 - M (M (basis 2)) 0) * B 1 +
      (M (M (basis 1)) 0 - M (M (basis 0)) 1) * B 2 := by
  have comp (v : Space) (i : Fin 3) :
      M₂ v B i = μ * H v i - M (M v) i + tApply (M₂ v) B i + tApply M (M v) i := by
    have := congrArg (fun w : Space => w i) (hE v)
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at this
    linarith
  have hHc (i j : Fin 3) : H (basis i) j = H (basis j) i := hH i j
  have tS (i j : Fin 3) : tApply (M₂ (basis i)) B j = tApply (M₂ (basis j)) B i := by
    rw [tApply_coords, tApply_coords, hsym (basis i) (basis j)]
  have tM (i j : Fin 3) : tApply M (M (basis i)) j = tApply M (M (basis j)) i := by
    rw [tApply_coords, tApply_coords]; ring
  rw [inner_curl_coords]
  simp only [hsym B]
  rw [comp (basis 1) 2, comp (basis 2) 1, comp (basis 2) 0, comp (basis 0) 2, comp (basis 0) 1,
    comp (basis 1) 0, hHc 1 2, hHc 2 0, hHc 0 1, tS 1 2, tS 2 0, tS 0 1, tM 1 2, tM 2 0, tM 0 1]
  ring

/-- **The secular identity (pointwise algebra).** With `M = DB` trace free, `M₂ = D²B`
symmetric, `H` symmetric, the force balance `M B − Mᵀ B = μ g` and its derivative in every
direction, the derivative of `J∥ = ⟪curl M, B⟫/|B|²` along `B`,
`(⟪curl (M₂ B), B⟫ + ⟪curl M, M B⟫)/|B|² − ⟪curl M, B⟫ · 2⟪B, M B⟫/|B|⁴`, equals
`2μ ⟪B × g, κ⟫/|B|²` with `κ` the field-line curvature. -/
theorem secular_algebra (M : Space →L[ℝ] Space) (M₂ : Space →L[ℝ] Space →L[ℝ] Space)
    (H : Space →L[ℝ] Space) (B g : Space) (μ : ℝ) (hsym : ∀ u v, M₂ u v = M₂ v u)
    (hH : CoordSymm H)
    (hE : ∀ v, M₂ v B + M (M v) - tApply (M₂ v) B - tApply M (M v) = μ • H v)
    (hfb : M B - tApply M B = μ • g) (htr : divergence M = 0) (hB : B ≠ 0) :
    (⟪curl (M₂ B), B⟫ + ⟪curl M, M B⟫) / ‖B‖ ^ 2 -
        ⟪curl M, B⟫ * (2 * ⟪B, M B⟫) / (‖B‖ ^ 2) ^ 2 =
      2 * μ * ⟪cross B g, fieldLineCurvature B (M B)⟫ / ‖B‖ ^ 2 := by
  have hn : ‖B‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hB)
  have hκ : ⟪cross B g, fieldLineCurvature B (M B)⟫ = ⟪cross B g, M B⟫ / ‖B‖ ^ 2 := by
    rw [fieldLineCurvature, real_inner_smul_right, inner_sub_right, real_inner_smul_right,
      inner_cross_self_left]
    field_simp
    ring
  have hμ : μ * ⟪cross B g, M B⟫ = ⟪cross B (M B - tApply M B), M B⟫ := by
    rw [hfb, ← real_inner_smul_left]
    congr 1
    obtain ⟨a0, a1, a2⟩ := BallooningSurface.cross_coords B g
    obtain ⟨d0, d1, d2⟩ := BallooningSurface.cross_coords B (μ • g)
    apply space_ext
    · rw [d0, PiLp.smul_apply, a0]; simp only [PiLp.smul_apply, smul_eq_mul]; ring
    · rw [d1, PiLp.smul_apply, a1]; simp only [PiLp.smul_apply, smul_eq_mul]; ring
    · rw [d2, PiLp.smul_apply, a2]; simp only [PiLp.smul_apply, smul_eq_mul]; ring
  have key : ‖B‖ ^ 2 * (⟪curl (M₂ B), B⟫ + ⟪curl M, M B⟫) - ⟪curl M, B⟫ * (2 * ⟪B, M B⟫) =
      2 * ⟪cross B (M B - tApply M B), M B⟫ := by
    rw [inner_curl_dir M M₂ H B μ hsym hH hE, inner_curl_coords, inner_curl_coords,
      norm_sq_coords, inner_coords B (M B), inner_coords (cross _ _) (M B)]
    obtain ⟨c0, c1, c2⟩ := BallooningSurface.cross_coords B (M B - tApply M B)
    rw [c0, c1, c2]
    simp only [PiLp.sub_apply, tApply_coords, clm_coords M B, clm_coords M (M (basis 0)),
      clm_coords M (M (basis 1)), clm_coords M (M (basis 2))]
    rw [divergence_apply] at htr
    linear_combination (-(B 0 ^ 2 + B 1 ^ 2 + B 2 ^ 2) * ((M (basis 1) 2 - M (basis 2) 1) * B 0 +
      (M (basis 2) 0 - M (basis 0) 2) * B 1 + (M (basis 0) 1 - M (basis 1) 0) * B 2)) * htr
  rw [hκ]
  field_simp
  linear_combination key - 2 * hμ

/-! ## The parallel current and its derivative -/

/-- The parallel current density `J∥ = ⟪curl M, B⟫/|B|²` (with `M = DB`, `μ₀ J = curl M`). -/
@[expose] def jparOf (M : Space →L[ℝ] Space) (B : Space) : ℝ := ⟪curl M, B⟫ / ‖B‖ ^ 2

/-- The derivative of `y ↦ J∥(M(y), B(y))` at a point with data `M`, `M₂ = DM`, `B`. -/
@[expose] def jparDeriv (M : Space →L[ℝ] Space) (M₂ : Space →L[ℝ] Space →L[ℝ] Space)
    (B : Space) : Space →L[ℝ] ℝ :=
  (‖B‖ ^ 2)⁻¹ • ((innerSL ℝ B).comp (curlCLM.comp M₂) + (innerSL ℝ (curl M)).comp M) -
    (⟪curl M, B⟫ * 2 / (‖B‖ ^ 2) ^ 2) • (innerSL ℝ B).comp M

/-- The derivative of `J∥` applied to a vector. -/
theorem jparDeriv_apply (M : Space →L[ℝ] Space) (M₂ : Space →L[ℝ] Space →L[ℝ] Space)
    (B v : Space) :
    jparDeriv M M₂ B v = (⟪curl (M₂ v), B⟫ + ⟪curl M, M v⟫) / ‖B‖ ^ 2 -
      ⟪curl M, B⟫ * (2 * ⟪B, M v⟫) / (‖B‖ ^ 2) ^ 2 := by
  simp only [jparDeriv, sub_apply, smul_apply, add_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, smul_eq_mul]
  rw [real_inner_comm (curlCLM (M₂ v)) B]
  change (‖B‖ ^ 2)⁻¹ * (⟪curl (M₂ v), B⟫ + ⟪curl M, M v⟫) -
    ⟪curl M, B⟫ * 2 / (‖B‖ ^ 2) ^ 2 * ⟪B, M v⟫ = _
  ring

/-- **`J∥` is differentiable** where `B ≠ 0`, if `B` has derivative `M(x)` and `M` has
derivative `M₂` at `x`. -/
theorem hasFDerivAt_jpar {Bf : Space → Space} {Mf : Space → Space →L[ℝ] Space}
    {M₂ : Space →L[ℝ] Space →L[ℝ] Space} {x : Space} (hB : HasFDerivAt Bf (Mf x) x)
    (hM : HasFDerivAt Mf M₂ x) (h0 : Bf x ≠ 0) :
    HasFDerivAt (fun y => jparOf (Mf y) (Bf y)) (jparDeriv (Mf x) M₂ (Bf x)) x := by
  have hn : ‖Bf x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr h0)
  have hc : HasFDerivAt (fun y => curl (Mf y)) (curlCLM.comp M₂) x :=
    curlCLM.hasFDerivAt.comp x hM
  have hnum := hc.inner ℝ hB
  have hinv := (hasDerivAt_inv hn).hasFDerivAt.comp x hB.norm_sq
  have h := hnum.mul hinv
  refine h.congr_fderiv ?_ |>.congr_of_eventuallyEq ?_
  · ext v
    rw [jparDeriv_apply]
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, fderivInnerCLM_apply,
      ContinuousLinearMap.prod_apply, smul_eq_mul, innerSL_apply_apply, Function.comp_apply]
    rw [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, nsmul_eq_mul]
    change _ + _ * (_ + ⟪curl (M₂ v), Bf x⟫) = _
    field_simp
    ring
  · exact Filter.Eventually.of_forall fun y => by simp [jparOf, div_eq_mul_inv]

/-! ## The differentiated force balance -/

/-- The transpose as a sum over the coordinate basis. -/
theorem tApply_eq_sum (L : Space →L[ℝ] Space) (w : Space) :
    tApply L w = ⟪w, L (basis 0)⟫ • basis 0 + ⟪w, L (basis 1)⟫ • basis 1 +
      ⟪w, L (basis 2)⟫ • basis 2 := by
  apply space_ext <;> simp [tApply, basis]

/-- **Derivative of the force balance.** If `M B − Mᵀ B = μ g` holds on a neighbourhood of `x`
(`M = DB`), then at `x`, in every direction `v`,
`M₂ v B + M (M v) − (M₂ v)ᵀ B − Mᵀ (M v) = μ H v` (`M₂ = DM`, `H = Dg`). -/
theorem force_balance_deriv {Bf gf : Space → Space} {Mf : Space → Space →L[ℝ] Space}
    {M₂ : Space →L[ℝ] Space →L[ℝ] Space} {H : Space →L[ℝ] Space} {U : Set Space} {x : Space}
    {μ : ℝ} (hU : U ∈ 𝓝 x) (hB : HasFDerivAt Bf (Mf x) x) (hM : HasFDerivAt Mf M₂ x)
    (hg : HasFDerivAt gf H x)
    (hfb : ∀ y ∈ U, Mf y (Bf y) - tApply (Mf y) (Bf y) = μ • gf y) (v : Space) :
    M₂ v (Bf x) + Mf x (Mf x v) - tApply (M₂ v) (Bf x) - tApply (Mf x) (Mf x v) = μ • H v := by
  have h1 := hM.clm_apply hB
  have hcol (i : Fin 3) := hM.clm_apply (hasFDerivAt_const (basis i) x)
  have hi (i : Fin 3) := (hB.inner ℝ (hcol i)).smul_const (basis i)
  have h2 := ((hi 0).add (hi 1)).add (hi 2)
  have hφ := (h1.sub h2).sub (hg.const_smul μ)
  have hzero : HasFDerivAt (fun y => Mf y (Bf y) - (⟪Bf y, Mf y (basis 0)⟫ • basis 0 +
      ⟪Bf y, Mf y (basis 1)⟫ • basis 1 + ⟪Bf y, Mf y (basis 2)⟫ • basis 2) - μ • gf y)
      (0 : Space →L[ℝ] Space) x := by
    refine (hasFDerivAt_const (0 : Space) x).congr_of_eventuallyEq ?_
    filter_upwards [hU] with y hy
    rw [← tApply_eq_sum, hfb y hy, sub_self]
  have hD := congrArg (fun L : Space →L[ℝ] Space => L v) (hφ.unique hzero)
  simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, fderivInnerCLM_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.smulRight_apply, zero_apply, map_zero, zero_add] at hD
  rw [tApply_eq_sum, tApply_eq_sum, ← sub_eq_zero, ← hD]
  simp only [add_smul]
  abel

/-- **A gradient has a coordinate-symmetric derivative.** If `ψ` is `C²` at `x` with gradient
`g` on a neighbourhood of `x`, then `g` is differentiable at `x` with a coordinate-symmetric
derivative (the Hessian). -/
theorem hasFDerivAt_grad_symm {ψ : Space → ℝ} {gf : Space → Space} {V : Set Space}
    {x : Space} (hV : V ∈ 𝓝 x) (hψ : ContDiffAt ℝ 2 ψ x)
    (hgrad : ∀ y ∈ V, HasFDerivAt ψ (innerSL ℝ (gf y)) y) :
    ∃ G : Space →L[ℝ] Space, HasFDerivAt gf G x ∧ CoordSymm G := by
  set H := fderiv ℝ (fderiv ℝ ψ) x
  have hH : HasFDerivAt (fderiv ℝ ψ) H x :=
    ((hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hsymm := hψ.isSymmSndFDerivAt (by simp)
  have hfd : ∀ y ∈ V, fderiv ℝ ψ y = innerSL ℝ (gf y) := fun y hy => (hgrad y hy).fderiv
  have hcoord : ∀ k : Fin 3, HasFDerivAt (fun y => gf y k)
      ((ContinuousLinearMap.apply ℝ ℝ (basis k)).comp H) x := by
    intro k
    have h1 : HasFDerivAt (fun y => fderiv ℝ ψ y (basis k))
        ((ContinuousLinearMap.apply ℝ ℝ (basis k)).comp H) x :=
      (ContinuousLinearMap.apply ℝ ℝ (basis k)).hasFDerivAt.comp x hH
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hV] with y hy
    rw [hfd y hy, innerSL_apply_apply]
    fin_cases k <;> simp [basis, inner_coords]
  refine ⟨_, hasFDerivAt_of_coords hcoord, fun i j => ?_⟩
  rw [coords_apply, coords_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  exact hsymm _ _

/-! ## The secular transport theorem -/

/-- **`B · ∇J∥ = 2μ ⟪B × g, κ⟫/|B|²`.** Let `B` have derivative `M(y)` near `x`, `M` have a
symmetric derivative `M₂` at `x` (`B` is `C²`), `g` have a coordinate-symmetric derivative at
`x` (a gradient), `∇ · B = 0` at `x`, `B(x) ≠ 0`, and let the force balance
`M B − Mᵀ B = μ g` (i.e. `(curl B) × B = μ ∇ψ`) hold on a neighbourhood of `x`. Then the
derivative of the parallel current `J∥ = ⟪curl B, B⟫/|B|²` along `B` is `2μ ⟪B × g, κ⟫/|B|²`,
`κ` the field-line curvature: minus the secular coefficient of the ballooning drive `eikQ`.
This is `∇ · J = 0` for `J = J∥ B + B × ∇p/|B|²`, derived here from the second derivatives. -/
theorem jpar_transport {Bf gf : Space → Space} {Mf : Space → Space →L[ℝ] Space}
    {M₂ : Space →L[ℝ] Space →L[ℝ] Space} {G : Space →L[ℝ] Space} {U : Set Space} {x : Space}
    {μ : ℝ} (hU : U ∈ 𝓝 x) (hB : HasFDerivAt Bf (Mf x) x) (hM : HasFDerivAt Mf M₂ x)
    (hsym : ∀ u v, M₂ u v = M₂ v u) (hg : HasFDerivAt gf G x) (hG : CoordSymm G)
    (hfb : ∀ y ∈ U, Mf y (Bf y) - tApply (Mf y) (Bf y) = μ • gf y)
    (htr : divergence (Mf x) = 0) (h0 : Bf x ≠ 0) :
    jparDeriv (Mf x) M₂ (Bf x) (Bf x) =
      2 * μ * ⟪cross (Bf x) (gf x), fieldLineCurvature (Bf x) (Mf x (Bf x))⟫ / ‖Bf x‖ ^ 2 := by
  rw [jparDeriv_apply]
  exact secular_algebra _ _ G _ _ μ hsym hG (force_balance_deriv hU hB hM hg hfb)
    (hfb x (mem_of_mem_nhds hU)) htr h0

/-! ## Secular surface certificates -/

/-- **Secular surface certificate theorem.** In the setting of
`BallooningSurface.eikLine_stable_of_surfaceCert`, let `j` be a `C¹` function along the line
whose derivative along `B` is `2μ ⟪B × g, κ⟫/|B|²` (e.g. `J∥`, `jpar_transport`), `c₀` a
constant and `F(x, s)` a `C¹` function. If at every point of the line and every `s`

  `DF(x, s)(B, d) + d (c₀ − j) + ((c₀ − j) s + F)²/P ≤ −2μ ⟪g, κ⟫/|g|²`,

then every eikonal family of the line is stable. The certificate is
`Φ = (c₀ − j(x)) s + F(x, s)`; its secular part cancels the secular drive exactly, so the
condition involves only the normal-curvature drive. -/
theorem eikLine_stable_of_secularCert {X : ℝ → Space} {Bf gf κf : Space → Space} {μ : ℝ}
    {d : Space → ℝ} {σ : ℝ → ℝ} (hX : ∀ t, HasDerivAt X (Bf (X t)) t)
    (hB0 : ∀ t, Bf (X t) ≠ 0) (hg0 : ∀ t, gf (X t) ≠ 0) (hBg : ∀ t, ⟪Bf (X t), gf (X t)⟫ = 0)
    (hBc : Continuous fun t => Bf (X t)) (hgc : Continuous fun t => gf (X t))
    (hκc : Continuous fun t => κf (X t)) (hdc : Continuous fun t => d (X t))
    (hσ : ∀ t, HasDerivAt σ (d (X t)) t)
    {jf : Space → ℝ} {Dj : Space → (Space →L[ℝ] ℝ)}
    (hj : ∀ t, HasFDerivAt jf (Dj (X t)) (X t)) (hDj : Continuous fun t => Dj (X t))
    (hjB : ∀ t, Dj (X t) (Bf (X t)) =
      2 * μ * ⟪cross (Bf (X t)) (gf (X t)), κf (X t)⟫ / ‖Bf (X t)‖ ^ 2)
    (c₀ : ℝ) {F : Space × ℝ → ℝ} {DF : Space × ℝ → (Space × ℝ →L[ℝ] ℝ)}
    (hF : ∀ t s, HasFDerivAt F (DF (X t, s)) (X t, s))
    (hDF : Continuous fun p : ℝ × ℝ => DF (X p.1, p.2))
    (hcert : ∀ t s, DF (X t, s) (Bf (X t), d (X t)) + d (X t) * (c₀ - jf (X t)) +
      ((c₀ - jf (X t)) * s + F (X t, s)) ^ 2 / eikP (Bf (X t)) (gf (X t)) s ≤
      -(2 * μ * ⟪gf (X t), κf (X t)⟫) / ‖gf (X t)‖ ^ 2)
    (c : ℝ) :
    (eikLine X Bf gf κf μ σ c hB0 hg0 hBg hBc hgc hκc
      (continuous_iff_continuousAt.mpr fun t => (hσ t).continuousAt)).Stable := by
  set fst := ContinuousLinearMap.fst ℝ Space ℝ
  set snd := ContinuousLinearMap.snd ℝ Space ℝ
  have hXc : Continuous X := continuous_iff_continuousAt.mpr fun t => (hX t).continuousAt
  have hjc : Continuous fun t => jf (X t) :=
    continuous_iff_continuousAt.mpr fun t => (hj t).continuousAt.comp hXc.continuousAt
  refine eikLine_stable_of_surfaceCert (Φ := fun p => (c₀ - jf p.1) * p.2 + F p)
    (DΦ := fun p => (-p.2) • (Dj p.1).comp fst + (c₀ - jf p.1) • snd + DF p) hX hB0 hg0 hBg
    hBc hgc hκc hdc hσ ?_ ?_ ?_ c
  · intro t s
    have h1 : HasFDerivAt (fun p : Space × ℝ => jf p.1) ((Dj (X t)).comp fst) (X t, s) :=
      (hj t).comp (X t, s) hasFDerivAt_fst
    have h2 := ((h1.const_sub c₀).mul hasFDerivAt_snd).add (hF t s)
    refine h2.congr_fderiv ?_
    ext v <;> simp [fst, snd]
  · have e1 : Continuous fun p : ℝ × ℝ => -p.2 := continuous_snd.neg
    have e2 : Continuous fun p : ℝ × ℝ => (Dj (X p.1)).comp fst :=
      (hDj.comp continuous_fst).clm_comp continuous_const
    have e3 : Continuous fun p : ℝ × ℝ => c₀ - jf (X p.1) :=
      continuous_const.sub (hjc.comp continuous_fst)
    exact ((e1.smul e2).add (e3.smul continuous_const)).add hDF
  · intro t s
    have := hcert t s
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul, fst, snd,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', hjB t]
    unfold eikQ
    rw [neg_div, neg_div] at *
    linarith

/-! ## Sanity checks -/

/-- Degenerate case: a field with zero derivative carries no parallel current. -/
theorem jparOf_zero (B : Space) : jparOf 0 B = 0 := by
  simp [jparOf, curl]

/-- Special case: for the rigid rotation `B = ω × x` (`M = ω ×`, `curl M = 2ω`),
`J∥ = 2⟪ω, B⟫/|B|²`. -/
theorem jparOf_rotation (ω B : Space) :
    jparOf (crossBilinear ω) B = 2 * ⟪ω, B⟫ / ‖B‖ ^ 2 := by
  rw [jparOf, curl_rotation, real_inner_smul_left]

/-- Degenerate case of the secular certificate: with no pressure gradient (`μ = 0`), `j = 0`,
`c₀ = 0` and `F = 0` certify every eikonal family of every line. -/
theorem eikLine_secular_noDrive_stable {X : ℝ → Space} {Bf gf κf : Space → Space}
    {d : Space → ℝ} {σ : ℝ → ℝ} (hX : ∀ t, HasDerivAt X (Bf (X t)) t)
    (hB0 : ∀ t, Bf (X t) ≠ 0) (hg0 : ∀ t, gf (X t) ≠ 0) (hBg : ∀ t, ⟪Bf (X t), gf (X t)⟫ = 0)
    (hBc : Continuous fun t => Bf (X t)) (hgc : Continuous fun t => gf (X t))
    (hκc : Continuous fun t => κf (X t)) (hdc : Continuous fun t => d (X t))
    (hσ : ∀ t, HasDerivAt σ (d (X t)) t) (c : ℝ) :
    (eikLine X Bf gf κf 0 σ c hB0 hg0 hBg hBc hgc hκc
      (continuous_iff_continuousAt.mpr fun t => (hσ t).continuousAt)).Stable :=
  eikLine_stable_of_secularCert (jf := fun _ => 0) (Dj := fun _ => 0) (F := fun _ => 0)
    (DF := fun _ => 0) hX hB0 hg0 hBg hBc hgc hκc hdc hσ (fun _ => hasFDerivAt_const _ _)
    continuous_const (fun _ => by simp) 0 (fun _ _ => hasFDerivAt_const _ _) continuous_const
    (fun _ _ => by simp) c

end PlasmaLean.Stability.BallooningSecular
