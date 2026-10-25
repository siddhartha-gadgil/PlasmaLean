/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2Coords
public import PlasmaLean.Theory.Stability.BallooningSurface

/-!
# Ideal ballooning of Landreman's family 2: line data from the actual field and reduction

For Landreman's explicit finite-β, non-axisymmetric MHS equilibrium of family 2
(arXiv:2609.26742 v2, §3; `LandremanFamily2`) this module builds the data of the SUPPLIED
ballooning reduction (`BallooningReduction`) along every field line, from the actual field,
its actual Fréchet derivative, the actual pressure gradient and the actual curvature, and
reduces ballooning stability of all field lines and all eikonal families of a flux surface
to ONE pointwise inequality on `surface × ℝ` (`family2_stable_of_cert`).

## The supplied reduction (stated, not formalized)

High-`n` ideal ballooning modes `ξ = X exp(i n S)`, `B · ∇S = 0` (Connor–Hastie–Taylor 1978,
Dewar–Glasser 1983): a flux surface is ballooning stable iff for every field line and every
eikonal `S` the line energy `∫ (P X'² + Q X²) dt` is nonnegative for all compactly supported
`X`, with `P = |k|²/(ℓ|B|²)`, `Q = −2ℓ (B × k · μ₀∇p)(B × k · κ)/|B|⁴`, `k = ∇S` along the
line (`LineData.Stable`). Only this equivalence is supplied; everything below is proved.

## Proved here (`ε = 1/4`, `S = 4`, every `λ > 0` unless stated)

* Smoothness: `contDiffAt_field`, `contDiffAt_psi` (`C^∞` on `𝒰`), `isOpen_U`; hence the
  actual derivative `fieldDeriv` and `gradPsi` are continuous on `𝒰`
  (`continuousOn_fieldDeriv`, `continuousOn_gradPsi`).
* `hessian_transport`: along `B`, `∇ψ` is transported, `D(∇ψ) B = −(DB)ᵀ ∇ψ` (symmetric
  Hessian of the explicit `ψ`).
* `family2_eik_transport`: on every field line `X' = B(X)` in `𝒰`, for every `σ` with
  `σ' = d(X)` (`d = shear2`, the local shear built from `DB`) and every shift `c`,
  `k = k₀(X) − (σ − c)∇ψ(X)`, `k₀ = B × ∇ψ/|∇ψ|²`, is a transported eikonal gradient
  (`k' = −(DB)ᵀ k`, `k · B = 0`): exactly the covering-space `∇S` of the reduction, every
  `θ_k` being a shift `c` (`BallooningSurface.hasDerivAt_eik`).
* `field_ne_of_shell`, `gradPsi_ne_of_shell`: `B ≠ 0`, `∇ψ ≠ 0` on the shell
  `0 < ψ ≤ (19/20)²/2` of the region `R` (closed forms `Bsq > 0`, `gp2 > 0` at the coordinate
  point `coordMap (coordInv x) = x`).
* `family2Line`: the line data (`ℓ = 1`, actual `B`, transported `k`, `μ₀∇p` from
  `pressureGrad`, actual curvature `fieldLineCurvature B (DB B)`) of a field line in the shell;
  `family2Line_P`, `family2Line_Q`: `P = 1/|∇ψ|² + s²|∇ψ|²/|B|²`,
  `Q = (2/λ²)⟪∇ψ, κ⟫/|∇ψ|² + s (2/λ²)⟪B × ∇ψ, κ⟫/|B|²` (normal and geodesic curvature);
  `eikP_surfPt`: on the coordinate surface `P = 1/gp2 + s² gp2/Bsq` (closed forms).
* `family2_stable_of_cert`: a `C¹` certificate `Φ(x, s)` with
  `DΦ(x, s)(B(x), d(x)) + Φ²/P ≤ Q` at the points of a field line gives ballooning stability
  of that line for EVERY eikonal family.

## Status of the verdict (honest)

Numerically (UNTRUSTED `scripts/landreman_family2_ballooning_oracle.py`) every scanned
field line and eikonal family on the surfaces `k = 0.70 … 0.90` of the `λ = 200` Mercier band
is ballooning STABLE; the binding constraint is the large-`σ` (Mercier-type) tail, whose
averaged condition reproduces the Mercier threshold `k_c ≈ 0.54`. No certificate `Φ` is
supplied here: the only certificates affine in `s` are infeasible (oracle), and a genuinely
`s`-dependent `Φ` on the 2-torus resolving the `O(1/λ)` structure of `|∇ψ|` near the tips of
the flat cross-section is beyond this module. Hence **no ballooning-stability theorem for
family 2 is claimed**; this module is the reduction to a pointwise inequality.
-/

open scoped RealInnerProductSpace

public section
noncomputable section

namespace PlasmaLean.Design.LandremanFamily2Ballooning

open Set Filter Topology WithLp
open PlasmaLean.Fields PlasmaLean.Stability PlasmaLean.Stability.BallooningInfinite
open PlasmaLean.Stability.BallooningReduction PlasmaLean.Stability.BallooningSurface
open PlasmaLean.Design.LandremanFamily2 PlasmaLean.Design.LandremanFamily2Surface
open PlasmaLean.Design.LandremanFamily2Coords

/-! ## Smoothness of the explicit field and flux function -/

section Smooth
variable (ε S lam : ℝ) {n : WithTop ℕ∞}

/-- `Re Z` is smooth. -/
theorem contDiff_Zr : ContDiff ℝ n (Zr ε) := by
  have : Zr ε = fun x : Space => (x 0 ^ 2 + x 1 ^ 2) ^ 2 + ε * (x 0 ^ 2 - x 1 ^ 2) := by
    funext x; rfl
  rw [this]; fun_prop

/-- `Im Z` is smooth. -/
theorem contDiff_Zi : ContDiff ℝ n (Zi ε) := by
  have : Zi ε = fun x : Space => 2 * ε * x 0 * x 1 := by funext x; rfl
  rw [this]; fun_prop

variable {ε} {x : Space}

/-- `|Z|` is smooth on `𝒰`. -/
theorem contDiffAt_Mo (hx : x ∈ U ε) : ContDiffAt ℝ n (Mo ε) x := by
  have hZ : Zr ε x ^ 2 + Zi ε x ^ 2 ≠ 0 := by
    rw [← Mo_sq]; exact pow_ne_zero 2 (Mo_pos hx).ne'
  have : Mo ε = fun y => √(Zr ε y ^ 2 + Zi ε y ^ 2) := rfl
  rw [this]
  exact ((contDiff_Zr ε).contDiffAt.pow 2 |>.add ((contDiff_Zi ε).contDiffAt.pow 2)).sqrt hZ

/-- `σ` is smooth on `𝒰`. -/
theorem contDiffAt_sg (hx : x ∈ U ε) : ContDiffAt ℝ n (sg ε) x := by
  have hM : (Mo ε x + Zr ε x) / 2 ≠ 0 := by have : 0 < Mo ε x + Zr ε x := hx; positivity
  have : sg ε = fun y => √((Mo ε y + Zr ε y) / 2) := rfl
  rw [this]
  exact (((contDiffAt_Mo hx).add (contDiff_Zr ε).contDiffAt).div_const 2).sqrt hM

/-- `ν` is smooth on `𝒰`. -/
theorem contDiffAt_nu (hx : x ∈ U ε) : ContDiffAt ℝ n (nu ε) x := by
  have : nu ε = fun y => ε * y 0 * y 1 / sg ε y := rfl
  rw [this]
  exact ContDiffAt.div (by fun_prop) (contDiffAt_sg hx) (sg_pos hx).ne'

/-- `Re v` is smooth on `𝒰`. -/
theorem contDiffAt_vR (hx : x ∈ U ε) : ContDiffAt ℝ n (vR ε S lam) x := by
  have hs := contDiffAt_sg (n := n) hx
  have hn := contDiffAt_nu (n := n) hx
  have : vR ε S lam = fun y => Real.cos (lam * y 2) * Real.sin (sg ε y - S) *
      Real.cosh (nu ε y) + Real.sin (lam * y 2) * Real.cos (sg ε y - S) * Real.sinh (nu ε y) :=
    rfl
  rw [this]
  fun_prop

/-- The flux label `ψ` is smooth on `𝒰`. -/
theorem contDiffAt_psi (hx : x ∈ U ε) : ContDiffAt ℝ n (psi ε S lam) x := by
  have hv := contDiffAt_vR (n := n) S lam hx
  have : psi ε S lam = fun y => (Real.sin (lam * y 2) ^ 2 + vR ε S lam y ^ 2) / 2 := rfl
  rw [this]
  fun_prop

/-- The field is smooth on `𝒰`. -/
theorem contDiffAt_field (hx : x ∈ U ε) : ContDiffAt ℝ n (field ε S lam) x := by
  have hs := contDiffAt_sg (n := n) hx
  have hn := contDiffAt_nu (n := n) hx
  have hm : 2 * Mq ε x ≠ 0 := by have := Mq_pos hx; positivity
  have hv := contDiffAt_vR (n := n) S lam hx
  have hMq : ContDiffAt ℝ n (fun y => 2 * Mq ε y) x := by unfold Mq; fun_prop
  have huR : ContDiffAt ℝ n (uR ε S lam) x := by unfold uR cz sz; fun_prop
  have huI : ContDiffAt ℝ n (uI ε S lam) x := by unfold uI cz sz; fun_prop
  have hal : ContDiffAt ℝ n (al ε) x := by unfold al; fun_prop
  have hbe : ContDiffAt ℝ n (be ε) x := by unfold be; fun_prop
  refine contDiffAt_piLp' 2 fun i => ?_
  fin_cases i
  · simp only [field, Fin.zero_eta, Fin.isValue, PiLp.toLp_apply, Matrix.cons_val_zero]
    exact ContDiffAt.div (by fun_prop) hMq hm
  · simp only [field, Fin.mk_one, Fin.isValue, PiLp.toLp_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    exact ContDiffAt.div (by fun_prop) hMq hm
  · simp only [field, Fin.reduceFinMk, PiLp.toLp_apply, Fin.isValue, Matrix.cons_val]
    fun_prop

/-- The smooth region `𝒰` is open. -/
theorem isOpen_U (ε : ℝ) : IsOpen (U ε) := by
  have hc : Continuous fun x => Mo ε x + Zr ε x := by
    have h1 : Continuous (Zr ε) := (contDiff_Zr (n := 0) ε).continuous
    have h2 : Continuous (Zi ε) := (contDiff_Zi (n := 0) ε).continuous
    have : Mo ε = fun y => √(Zr ε y ^ 2 + Zi ε y ^ 2) := rfl
    rw [this]; fun_prop
  exact isOpen_lt continuous_const hc

/-- The actual derivative of the field is continuous on `𝒰`. -/
theorem continuousOn_fieldDeriv : ContinuousOn (fieldDeriv ε S lam) (U ε) := by
  have hcd : ContDiffOn ℝ 1 (field ε S lam) (U ε) :=
    fun _ hy => (contDiffAt_field S lam hy).contDiffWithinAt
  refine (hcd.continuousOn_fderiv_of_isOpen (isOpen_U ε) le_rfl).congr fun y hy => ?_
  exact ((field_hasFDerivAt ε S lam hy).fderiv).symm

/-- The gradient of `ψ` is continuous on `𝒰`. -/
theorem continuousOn_gradPsi : ContinuousOn (gradPsi ε S lam) (U ε) := by
  have hcd : ContDiffOn ℝ 1 (psi ε S lam) (U ε) :=
    fun _ hy => (contDiffAt_psi S lam hy).contDiffWithinAt
  have hf := hcd.continuousOn_fderiv_of_isOpen (isOpen_U ε) le_rfl
  have hcoord : ∀ y ∈ U ε, gradPsi ε S lam y =
      toLp 2 ![fderiv ℝ (psi ε S lam) y (basis 0), fderiv ℝ (psi ε S lam) y (basis 1),
        fderiv ℝ (psi ε S lam) y (basis 2)] := by
    intro y hy
    rw [(psi_hasFDerivAt ε S lam hy).fderiv]
    apply space_ext <;> simp [basis, BallooningSurface.inner_coords]
  refine ContinuousOn.congr ?_ hcoord
  have hi : ∀ i : Fin 3, ContinuousOn (fun y => fderiv ℝ (psi ε S lam) y (basis i)) (U ε) :=
    fun i => hf.clm_apply continuousOn_const
  have e : (fun y => toLp 2 ![fderiv ℝ (psi ε S lam) y (basis 0),
      fderiv ℝ (psi ε S lam) y (basis 1), fderiv ℝ (psi ε S lam) y (basis 2)]) =
      fun y => (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
        (fun i => fderiv ℝ (psi ε S lam) y (basis i)) := by
    funext y; apply space_ext <;> rfl
  rw [e]
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.continuous.comp_continuousOn
    (continuousOn_pi.mpr hi)

/-- The field is continuous on `𝒰`. -/
theorem continuousOn_field : ContinuousOn (field ε S lam) (U ε) :=
  fun _ hy => (contDiffAt_field (n := 0) S lam hy).continuousAt.continuousWithinAt

end Smooth

/-! ## Transport of `∇ψ` and of the eikonal -/

/-- `tApply` is the transpose `adjApply` of `LandremanEquilibrium`. -/
theorem tApply_eq_adjApply (M : Space →L[ℝ] Space) (v : Space) :
    tApply M v = LandremanEquilibrium.adjApply M v := rfl

/-- **`∇ψ` is transported along `B`**: on `𝒰` (`λ ≠ 0`), `D(∇ψ)(B) = −(DB)ᵀ ∇ψ`. -/
theorem hessian_transport {ε S lam : ℝ} (hl : lam ≠ 0) {x : Space} (hx : x ∈ U ε) :
    ∃ G : Space →L[ℝ] Space, HasFDerivAt (gradPsi ε S lam) G x ∧
      G (field ε S lam x) = -tApply (fieldDeriv ε S lam x) (gradPsi ε S lam x) :=
  transport_of_hessian ((isOpen_U ε).mem_nhds hx) (contDiffAt_psi S lam hx)
    (fun _ hy => psi_hasFDerivAt ε S lam hy) (fun _ hy => field_tangent_psi hl hy)
    (field_hasFDerivAt ε S lam hx)

/-- The local shear of family 2: `shearRate (DB) B ∇ψ`. -/
@[expose] def shear2 (ε S lam : ℝ) (x : Space) : ℝ :=
  shearRate (fieldDeriv ε S lam x) (field ε S lam x) (gradPsi ε S lam x)

/-- The actual field-line curvature `b · ∇b` of family 2. -/
@[expose] def kappa2 (ε S lam : ℝ) (x : Space) : Space :=
  fieldLineCurvature (field ε S lam x) (fieldDeriv ε S lam x (field ε S lam x))

/-- **The covering-space eikonal of family 2 is transported** along every field line in `𝒰`
on which `∇ψ ≠ 0`: `k' = −(DB)ᵀ k` with `k = k₀(X) − (σ − c)∇ψ(X)`, `σ' = d(X)`. -/
theorem family2_eik_transport {ε S lam : ℝ} (hl : lam ≠ 0) {X : ℝ → Space} {σ : ℝ → ℝ}
    {t : ℝ} (c : ℝ) (hX : HasDerivAt X (field ε S lam (X t)) t) (hU : X t ∈ U ε)
    (hg : gradPsi ε S lam (X t) ≠ 0) (hσ : HasDerivAt σ (shear2 ε S lam (X t)) t) :
    HasDerivAt (fun t => eik (field ε S lam (X t)) (gradPsi ε S lam (X t)) (σ t - c))
      (-tApply (fieldDeriv ε S lam (X t))
        (eik (field ε S lam (X t)) (gradPsi ε S lam (X t)) (σ t - c))) t := by
  obtain ⟨G, hG, hGB⟩ := hessian_transport (S := S) hl hU
  have htr : divergence (fieldDeriv ε S lam (X t)) = 0 := by
    have := field_divergence_free (S := S) hl hU
    rwa [(field_hasFDerivAt ε S lam hU).fderiv] at this
  exact hasDerivAt_eik hX (field_hasFDerivAt ε S lam hU) hG hGB htr
    (field_tangent_psi hl hU) hg hσ

/-! ## Nonvanishing on the shell -/

section Shell
variable {lam : ℝ}

/-- A shell point is the coordinate point of its inverse coordinates, with `0 < k ≤ 19/20`. -/
theorem shell_eq_surfPt (hl : 0 < lam) {x : Space} (hx : x ∈ shell lam (19 / 20)) :
    0 < kOf lam x ∧ kOf lam x ≤ 19 / 20 ∧
      x = surfPt (1 / 4) 4 lam (kOf lam x) (chiOf lam x) (zetaOf x) := by
  have hm := coordMap_coordInv hl (by norm_num) le_rfl hx
  obtain ⟨-, hψ0, hψ1⟩ := hx
  refine ⟨Real.sqrt_pos.mpr (by linarith), ?_, ?_⟩
  · rw [kOf, Real.sqrt_le_left (by norm_num)]; linarith
  · conv_lhs => rw [← hm]
    simp [coordMap]

/-- `B ≠ 0` on the shell. -/
theorem field_ne_of_shell (hl : 0 < lam) {x : Space} (hx : x ∈ shell lam (19 / 20)) :
    field (1 / 4) 4 lam x ≠ 0 := by
  obtain ⟨hk0, hk1, hxe⟩ := shell_eq_surfPt hl hx
  intro h
  have := normSq_field_surfPt (χ := chiOf lam x) (ζ := zetaOf x) hl.ne' hk0 hk1
  rw [← hxe, h, norm_zero] at this
  have hp := Bsq_pos (ε := 1 / 4) (S := 4) (lam := lam) (s1 := Real.sin (chiOf lam x))
    (c1 := Real.cos (chiOf lam x)) (s2 := Real.sin (2 * zetaOf x)) (by norm_num)
    (Real.abs_cos_le_one (2 * zetaOf x)) (k_sq_lt_one hk0 hk1)
  linarith

/-- `∇ψ ≠ 0` on the shell. -/
theorem gradPsi_ne_of_shell (hl : 0 < lam) {x : Space} (hx : x ∈ shell lam (19 / 20)) :
    gradPsi (1 / 4) 4 lam x ≠ 0 := by
  obtain ⟨hk0, hk1, hxe⟩ := shell_eq_surfPt hl hx
  intro h
  have := normSq_gradPsi_surfPt (χ := chiOf lam x) (ζ := zetaOf x) hl.ne' hk0 hk1
  rw [← hxe, h, norm_zero] at this
  have hp := gp2_pos (ε := 1 / 4) (S := 4) (s2 := Real.sin (2 * zetaOf x))
    (Real.sin_sq_add_cos_sq (chiOf lam x)) (by norm_num)
    (Real.abs_cos_le_one (2 * zetaOf x)) hk0 (k_sq_lt_one hk0 hk1) hl.ne'
  linarith

/-- Shell points lie in `𝒰`. -/
theorem mem_U_of_shell {x : Space} (hx : x ∈ shell lam (19 / 20)) : x ∈ U (1 / 4) :=
  hx.1.1

end Shell

/-! ## The line data of family 2 -/

/-- Hypotheses on a field line of family 2: `X' = B(X)` and `X` stays in the shell
`0 < ψ ≤ (19/20)²/2` of `R` (for `ψ ≤ 81/200` forward invariance is
`LandremanFamily2.fieldLine_confined`). -/
structure FieldLine (lam : ℝ) (X : ℝ → Space) : Prop where
  deriv : ∀ t, HasDerivAt X (field (1 / 4) 4 lam (X t)) t
  shell : ∀ t, X t ∈ shell lam (19 / 20)

namespace FieldLine
variable {lam : ℝ} {X : ℝ → Space}

/-- A field line is continuous. -/
theorem continuous (L : FieldLine lam X) : Continuous X :=
  continuous_iff_continuousAt.mpr fun t => (L.deriv t).continuousAt

/-- `t ↦ B(X t)` is continuous. -/
theorem cont_B (L : FieldLine lam X) : Continuous fun t => field (1 / 4) 4 lam (X t) :=
  continuous_iff_continuousAt.mpr fun t =>
    ((continuousOn_field _ _).continuousAt ((isOpen_U _).mem_nhds (L.shell t).1.1)).comp
      L.continuous.continuousAt

/-- `t ↦ ∇ψ(X t)` is continuous. -/
theorem cont_g (L : FieldLine lam X) : Continuous fun t => gradPsi (1 / 4) 4 lam (X t) :=
  continuous_iff_continuousAt.mpr fun t =>
    ((continuousOn_gradPsi _ _).continuousAt ((isOpen_U _).mem_nhds (L.shell t).1.1)).comp
      L.continuous.continuousAt

/-- `t ↦ DB(X t)` is continuous. -/
theorem cont_M (L : FieldLine lam X) : Continuous fun t => fieldDeriv (1 / 4) 4 lam (X t) :=
  continuous_iff_continuousAt.mpr fun t =>
    ((continuousOn_fieldDeriv _ _).continuousAt ((isOpen_U _).mem_nhds (L.shell t).1.1)).comp
      L.continuous.continuousAt

/-- `t ↦ κ(X t)` is continuous. -/
theorem cont_kappa (L : FieldLine lam X) (hl : 0 < lam) :
    Continuous fun t => kappa2 (1 / 4) 4 lam (X t) := by
  have hB := L.cont_B
  have hDBB : Continuous fun t => fieldDeriv (1 / 4) 4 lam (X t) (field (1 / 4) 4 lam (X t)) :=
    L.cont_M.clm_apply hB
  have hn : ∀ t, ‖field (1 / 4) 4 lam (X t)‖ ^ 2 ≠ 0 := fun t =>
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (field_ne_of_shell hl (L.shell t)))
  unfold kappa2 fieldLineCurvature
  exact ((hB.norm.pow 2).inv₀ hn).smul
    (hDBB.sub (((hB.inner hDBB).div (hB.norm.pow 2) hn).smul hB))

/-- `t ↦ d(X t)` (local shear) is continuous. -/
theorem cont_shear (L : FieldLine lam X) (hl : 0 < lam) :
    Continuous fun t => shear2 (1 / 4) 4 lam (X t) := by
  have hB := L.cont_B
  have hg := L.cont_g
  have hM := L.cont_M
  have hn : ∀ t, ‖gradPsi (1 / 4) 4 lam (X t)‖ ^ 2 ≠ 0 := fun t =>
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (gradPsi_ne_of_shell hl (L.shell t)))
  have hk : Continuous fun t => eikBase (field (1 / 4) 4 lam (X t)) (gradPsi (1 / 4) 4 lam (X t)) :=
    ((hg.norm.pow 2).inv₀ hn).smul (continuous_cross.comp (hB.prodMk hg))
  unfold shear2 shearRate
  exact ((hk.inner (hM.clm_apply hg)).add ((hM.clm_apply hk).inner hg)).div (hg.norm.pow 2) hn

end FieldLine

/-- `μ₀ ∇p = −∇ψ/λ²` (`μ₀ ≠ 0`): the pressure gradient on the eikonal family. -/
theorem mu0_pressureGrad {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (lam : ℝ) (x : Space) :
    μ₀ • pressureGrad μ₀ (1 / 4) 4 lam x = (-(lam ^ 2)⁻¹) • gradPsi (1 / 4) 4 lam x := by
  rw [pressureGrad, smul_smul]
  congr 1
  field_simp

/-- **The ballooning line data of family 2** along a field line `X` in the shell, for a
secular variable `σ` (`σ' = d(X)`) and shift `c` (the eikonal family): `ℓ = 1`, the actual
field, the transported eikonal `k₀(X) − (σ − c)∇ψ(X)` (`family2_eik_transport`),
`μ₀∇p = −∇ψ/λ²` (`mu0_pressureGrad`) and the actual curvature `kappa2`. -/
@[expose] def family2Line {lam : ℝ} (hl : 0 < lam) {X : ℝ → Space} (L : FieldLine lam X)
    {σ : ℝ → ℝ} (hσ : ∀ t, HasDerivAt σ (shear2 (1 / 4) 4 lam (X t)) t) (c : ℝ) : LineData :=
  eikLine X (field (1 / 4) 4 lam) (gradPsi (1 / 4) 4 lam) (kappa2 (1 / 4) 4 lam)
    (-(lam ^ 2)⁻¹) σ c (fun t => field_ne_of_shell hl (L.shell t))
    (fun t => gradPsi_ne_of_shell hl (L.shell t))
    (fun t => field_tangent_psi hl.ne' (L.shell t).1.1) L.cont_B L.cont_g (L.cont_kappa hl)
    (continuous_iff_continuousAt.mpr fun t => (hσ t).continuousAt)

section LineCoeffs
variable {lam : ℝ} (hl : 0 < lam) {X : ℝ → Space} (L : FieldLine lam X) {σ : ℝ → ℝ}
  (hσ : ∀ t, HasDerivAt σ (shear2 (1 / 4) 4 lam (X t)) t) (c : ℝ)

/-- The eikonal of `family2Line` is the transported covering-space gradient. -/
theorem family2Line_k_transport (t : ℝ) :
    HasDerivAt (family2Line hl L hσ c).k
      (-tApply (fieldDeriv (1 / 4) 4 lam (X t)) ((family2Line hl L hσ c).k t)) t :=
  family2_eik_transport hl.ne' c (L.deriv t) (L.shell t).1.1
    (gradPsi_ne_of_shell hl (L.shell t)) (hσ t)

/-- The eikonal of `family2Line` is orthogonal to `B`. -/
theorem family2Line_k_perp (t : ℝ) :
    ⟪(family2Line hl L hσ c).k t, (family2Line hl L hσ c).B t⟫ = 0 :=
  inner_eik_B (field_tangent_psi hl.ne' (L.shell t).1.1) _

/-- The pressure-gradient slot of `family2Line` is the actual `μ₀∇p` (every `μ₀ ≠ 0`). -/
theorem family2Line_gp {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (t : ℝ) :
    (family2Line hl L hσ c).gp t = μ₀ • pressureGrad μ₀ (1 / 4) 4 lam (X t) :=
  (mu0_pressureGrad hμ lam (X t)).symm

/-- **Bending coefficient** of family 2: `P = 1/|∇ψ|² + (σ − c)² |∇ψ|²/|B|²`. -/
theorem family2Line_P (t : ℝ) :
    (family2Line hl L hσ c).P t = eikP (field (1 / 4) 4 lam (X t))
      (gradPsi (1 / 4) 4 lam (X t)) (σ t - c) :=
  ballooningP_eik (field_tangent_psi hl.ne' (L.shell t).1.1)
    (gradPsi_ne_of_shell hl (L.shell t)) (field_ne_of_shell hl (L.shell t)) _

/-- **Drive** of family 2: `Q = (2/λ²)⟪∇ψ, κ⟫/|∇ψ|² + (σ − c)(2/λ²)⟪B × ∇ψ, κ⟫/|B|²`. -/
theorem family2Line_Q (t : ℝ) :
    (family2Line hl L hσ c).Q t = eikQ (-(lam ^ 2)⁻¹) (field (1 / 4) 4 lam (X t))
      (gradPsi (1 / 4) 4 lam (X t)) (kappa2 (1 / 4) 4 lam (X t)) (σ t - c) :=
  ballooningQ_eik (field_tangent_psi hl.ne' (L.shell t).1.1)
    (gradPsi_ne_of_shell hl (L.shell t)) (field_ne_of_shell hl (L.shell t)) _ _ _

end LineCoeffs

/-- On the coordinate surface `ψ = k²/2` the bending coefficient is the closed form
`1/gp2 + s² gp2/Bsq` of `LandremanFamily2Surface`. -/
theorem eikP_surfPt {lam k χ ζ : ℝ} (hl : lam ≠ 0) (hk0 : 0 < k) (hk1 : k ≤ 19 / 20) (s : ℝ) :
    eikP (field (1 / 4) 4 lam (surfPt (1 / 4) 4 lam k χ ζ))
        (gradPsi (1 / 4) 4 lam (surfPt (1 / 4) 4 lam k χ ζ)) s =
      1 / gp2 (1 / 4) 4 lam k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) +
        s ^ 2 * (gp2 (1 / 4) 4 lam k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ))
          (Real.cos (2 * ζ)) /
          Bsq (1 / 4) 4 lam k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ))) := by
  rw [eikP, normSq_field_surfPt hl hk0 hk1, normSq_gradPsi_surfPt hl hk0 hk1]

/-- **Reduction of family-2 ballooning to a surface inequality.** For a field line `X` in the
shell, a secular variable `σ' = d(X)`, and a `C¹` function `Φ(x, s)` with derivative `DΦ`
satisfying `DΦ(x, s)(B(x), d(x)) + Φ²/P ≤ Q` at the points of the line for all `s`, the line
is ballooning stable for EVERY eikonal family `c` (all `θ_k`), in the sense of the supplied
reduction. -/
theorem family2_stable_of_cert {lam : ℝ} (hl : 0 < lam) {X : ℝ → Space} (L : FieldLine lam X)
    {σ : ℝ → ℝ} (hσ : ∀ t, HasDerivAt σ (shear2 (1 / 4) 4 lam (X t)) t)
    {Φ : Space × ℝ → ℝ} {DΦ : Space × ℝ → (Space × ℝ →L[ℝ] ℝ)}
    (hΦ : ∀ t s, HasFDerivAt Φ (DΦ (X t, s)) (X t, s))
    (hDΦ : Continuous fun p : ℝ × ℝ => DΦ (X p.1, p.2))
    (hcert : ∀ t s, DΦ (X t, s) (field (1 / 4) 4 lam (X t), shear2 (1 / 4) 4 lam (X t)) +
      Φ (X t, s) ^ 2 / eikP (field (1 / 4) 4 lam (X t)) (gradPsi (1 / 4) 4 lam (X t)) s ≤
      eikQ (-(lam ^ 2)⁻¹) (field (1 / 4) 4 lam (X t)) (gradPsi (1 / 4) 4 lam (X t))
        (kappa2 (1 / 4) 4 lam (X t)) s)
    (c : ℝ) : (family2Line hl L hσ c).Stable :=
  eikLine_stable_of_surfaceCert L.deriv _ _ _ L.cont_B L.cont_g (L.cont_kappa hl)
    (L.cont_shear hl) hσ hΦ hDΦ hcert c

end PlasmaLean.Design.LandremanFamily2Ballooning
