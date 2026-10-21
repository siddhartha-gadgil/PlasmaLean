/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCSmooth
public import PlasmaLean.Design.RationalStellaratorFieldLines

/-!
# Exact invariant tori of a general vector field trap its field lines (toroidal geometry)

A field-independent version of `Design/RationalStellaratorForever` and
`Design/RationalStellaratorFieldLines` (which treat `field (1/4)` and torus A), for any vector field
`V : Space → Space` and the tube coordinates `rt, θs, φs` about the exact magnetic axis
`R = 1, z = 0`.

**Components.** `cR V R φ z`, `cT V R φ z`, `cZ V R φ z`: the cylindrical components
`V = c_R e_R + R c_T e_φ + c_z e_z` at `cylPt R φ z` (`V_cylPt`), and the toroidal components
`vRadV = cos α c_R + sin α c_z`, `vPolV = (cos α c_z − sin α c_R)/r`, `vTorV = c_T` at
`torPt r α φ` (`V_torPt`: `V` is the velocity of `t ↦ torPt (r + t v_r) (α + t v_α) (φ + t v_φ)`).
`fderiv_G_V_torPt`: for a torus profile `ρ` and `G = rt − ρ(θs, φs)`,
`DG · V = v_r − Dρ · (v_α, v_φ)`.

**Lipschitz collar bound.** If `V` is `C¹` on an open set containing the shell
`r₁ ≤ rt ≤ r₂` (`0 < r₁`, `r₂ < 1/2`), the defect `v_r − p_α v_α − p_φ v_φ` is uniformly
Lipschitz in `r` on the compact box `r ∈ [r₁, r₂]`, `α, φ ∈ [−4, 4]`, `|p| ≤ C`
(`exists_lipschitz_WV`; principal angles lie in `(−π, π]`).

**Flow tori.** `FlowTorus V ι ρmin ρmax Rk zk`: a `C²` torus `(θ, φ) ↦ (R, z)`, `2π`-periodic in
`θ`, `π`-periodic in `φ`, solving the flow form `c_T (∂_φ K + ι ∂_θ K) = (c_R, c_z)` exactly, with
`c_T > 0` on it, star-shaped in the flow angle (`(R − 1) cos θ + z sin θ > 0`), with positive
winding rate and `ρmin ≤ rt ≤ ρmax`. As for torus A it is a radial graph `rt = ρ(α, φ)` of a
`C¹` torus profile (`FlowTorus.profile`), tangent to `V` (`FlowTorus.tangent`).

**Main theorem** (`FlowTorus.confined_existsUnique`): if moreover `V` is `C¹` on an open set
containing the closed tube `rt ≤ R₁` (`ρmax < R₁ < 1/2`), then from every point on the axis or
inside the torus there is exactly one two-sided field line of `V`, defined for all time, and every
field line starting there stays inside the torus forever.

**Sanity.** `cR_field`: for `V = field (1/4)` the components are those of `field_cylPt`.
-/

open scoped RealInnerProductSpace

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open Real Set Filter Topology PlasmaLean.Fields PlasmaLean.Design.RationalStellarator
  PlasmaLean.Design.KamTorusA WithLp

/-! ## Cylindrical and toroidal components of a vector field -/

/-- The `e_R`-component of `V` at `cylPt R φ z`. -/
def cR (V : Space → Space) (R φ z : ℝ) : ℝ := ⟪V (cylPt R φ z), eRv φ⟫

/-- The angular rate `dφ/dt = ⟪V, e_φ⟫ / R` of `V` at `cylPt R φ z`. -/
def cT (V : Space → Space) (R φ z : ℝ) : ℝ := ⟪V (cylPt R φ z), ePv φ⟫ / R

/-- The `e_z`-component of `V` at `cylPt R φ z`. -/
def cZ (V : Space → Space) (R φ z : ℝ) : ℝ := ⟪V (cylPt R φ z), eZv⟫

/-- Inner products with the frame vectors. -/
theorem inner_frame (v : Space) (φ : ℝ) :
    ⟪v, eRv φ⟫ = v 0 * cos φ + v 1 * sin φ ∧ ⟪v, ePv φ⟫ = -(v 0 * sin φ) + v 1 * cos φ ∧
      ⟪v, eZv⟫ = v 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [eRv, inner_toLp3]; ring
  · rw [ePv, inner_toLp3]; ring
  · rw [eZv, inner_toLp3]; ring

/-- **Cylindrical decomposition** `V = c_R e_R + R c_T e_φ + c_z e_z` (`R ≠ 0`). -/
theorem V_cylPt (V : Space → Space) {R : ℝ} (hR : R ≠ 0) (φ z : ℝ) :
    V (cylPt R φ z) = toLp 2
      ![cR V R φ z * cos φ - R * cT V R φ z * sin φ, cR V R φ z * sin φ + R * cT V R φ z * cos φ,
        cZ V R φ z] := by
  obtain ⟨h1, h2, h3⟩ := inner_frame (V (cylPt R φ z)) φ
  have hcs := cos_sq_add_sin_sq φ
  simp only [cR, cT, cZ, h1, h2, h3]
  ext i; fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    field_simp
    linear_combination (-(V (cylPt R φ z) 0)) * hcs
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    field_simp
    linear_combination (-(V (cylPt R φ z) 1)) * hcs
  · simp

/-- **Sanity**: for `field (1/4)` the cylindrical components are `B^R`, `B^φ`, `B^z` of
`field_cylPt`. -/
theorem cR_field {R : ℝ} (hR : 0 < R) (φ z : ℝ) :
    cR (field (1 / 4)) R φ z = cylBR R z (cos (2 * φ)) (sin (2 * φ)) ∧
      cT (field (1 / 4)) R φ z = cylBT R z (cos (2 * φ)) (sin (2 * φ)) ∧
      cZ (field (1 / 4)) R φ z = cylBZ R z (cos (2 * φ)) (sin (2 * φ)) := by
  have hcs := cos_sq_add_sin_sq φ
  simp only [cR, cT, cZ, field_cylPt hR, eRv, ePv, eZv, inner_toLp3]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, mul_zero,
    add_zero, mul_one, zero_add]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination cylBR R z (cos (2 * φ)) (sin (2 * φ)) * hcs
  · field_simp
    linear_combination R * cylBT R z (cos (2 * φ)) (sin (2 * φ)) * hcs
  · rfl

/-- Radial component `v_r = cos α c_R + sin α c_z` at `torPt r α φ`. -/
def vRadV (V : Space → Space) (r α φ : ℝ) : ℝ :=
  cos α * cR V (1 + r * cos α) φ (r * sin α) + sin α * cZ V (1 + r * cos α) φ (r * sin α)

/-- Poloidal component `v_α = (cos α c_z − sin α c_R) / r`. -/
def vPolV (V : Space → Space) (r α φ : ℝ) : ℝ :=
  (cos α * cZ V (1 + r * cos α) φ (r * sin α) - sin α * cR V (1 + r * cos α) φ (r * sin α)) / r

/-- Toroidal component `v_φ = c_T`. -/
def vTorV (V : Space → Space) (r α φ : ℝ) : ℝ := cT V (1 + r * cos α) φ (r * sin α)

/-- **`V` in toroidal coordinates**: for `0 < r ≤ 1/2`, `V(torPt r α φ)` is the velocity of
`t ↦ torPt (r + t v_r) (α + t v_α) (φ + t v_φ)` at `t = 0`. -/
theorem V_torPt (V : Space → Space) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 2) (α φ : ℝ) :
    HasDerivAt (fun t => torPt (r + t * vRadV V r α φ) (α + t * vPolV V r α φ)
        (φ + t * vTorV V r α φ)) (V (torPt r α φ)) 0 := by
  have hR : 0 < 1 + r * cos α := by nlinarith [neg_one_le_cos α]
  set a := vRadV V r α φ with ha
  set b := vPolV V r α φ with hb
  set d := vTorV V r α φ with hd
  have hra := hasDerivAt_affine r a
  have hαb := hasDerivAt_affine α b
  have hφd := hasDerivAt_affine φ d
  have hRt := (hra.mul hαb.cos).const_add 1
  have k0 := hRt.mul hφd.cos
  have k1 := hRt.mul hφd.sin
  have k2 := hra.mul hαb.sin
  have hγ := hasDerivAt_toLp3 k0 k1 k2
  simp only [zero_mul, add_zero] at hγ
  rw [torPt, V_cylPt V hR.ne']
  convert hγ using 1
  · rfl
  have hcs := cos_sq_add_sin_sq α
  have hr0 : r ≠ 0 := hr.ne'
  have hBR : a * cos α - r * sin α * b = cR V (1 + r * cos α) φ (r * sin α) := by
    rw [ha, hb, vRadV, vPolV]
    generalize cR V (1 + r * cos α) φ (r * sin α) = BR
    generalize cZ V (1 + r * cos α) φ (r * sin α) = BZ
    field_simp
    linear_combination BR * hcs
  have hBZ : a * sin α + r * cos α * b = cZ V (1 + r * cos α) φ (r * sin α) := by
    rw [ha, hb, vRadV, vPolV]
    generalize cR V (1 + r * cos α) φ (r * sin α) = BR
    generalize cZ V (1 + r * cos α) φ (r * sin α) = BZ
    field_simp
    linear_combination BZ * hcs
  ext k
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.mul_apply,
      zero_mul, add_zero]
    rw [← hBR, hd, vTorV]; ring
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_zero, Pi.mul_apply, zero_mul, add_zero]
    rw [← hBR, hd, vTorV]; ring
  · simp only [Fin.reduceFinMk, Matrix.cons_val, Pi.mul_apply,
      zero_mul, add_zero]
    rw [← hBZ]; ring

/-- **`DG · V` in toroidal coordinates.** For a torus profile `ρ`, `G = rt − ρ(θs, φs)` and
`0 < r < 1/2`: `DG · V = v_r − Dρ(α, φ) · (v_α, v_φ)` at `torPt r α φ`. -/
theorem fderiv_G_V_torPt (V : Space → Space) {ρ : ℝ → ℝ → ℝ} (hρ : TorusProfile ρ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1 / 2) (α φ : ℝ) :
    fderiv ℝ (fun x => rt x - ρ (θs x) (φs x)) (torPt r α φ) (V (torPt r α φ)) =
      vRadV V r α φ - fderiv ℝ (fun p : ℝ × ℝ => ρ p.1 p.2) (α, φ)
        (vPolV V r α φ, vTorV V r α φ) := by
  set a := vRadV V r α φ
  set b := vPolV V r α φ
  set d := vTorV V r α φ
  have hrt := rt_torPt hr.le (by linarith) α φ
  have hGd : DifferentiableAt ℝ (fun x => rt x - ρ (θs x) (φs x)) (torPt r α φ) :=
    TubeCoords.differentiableAt_G (c := tube) hρ
      ⟨show rt (torPt r α φ) < 1 / 2 by rw [hrt]; exact hr1,
        show 0 < rt (torPt r α φ) by rw [hrt]; exact hr⟩
  have hγ := V_torPt V hr hr1.le α φ
  have h1 := hGd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp)
  have hcurve : HasDerivAt (fun t : ℝ => (α + t * b, φ + t * d)) (b, d) 0 :=
    (hasDerivAt_affine α b).prodMk (hasDerivAt_affine φ d)
  have h2 := (hasDerivAt_affine r a).sub
    ((hρ.differentiable (α, φ)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hcurve (by simp))
  refine h1.unique (h2.congr_of_eventuallyEq ?_)
  have hc : ContinuousAt (fun t : ℝ => r + t * a) 0 := (hasDerivAt_affine r a).continuousAt
  filter_upwards [hc.preimage_mem_nhds (Ioo_mem_nhds (a := 0) (b := 1 / 2)
    (by simpa using hr) (by simpa using hr1))] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  simp only [Function.comp_apply]
  rw [rt_torPt ht0.le (by linarith)]
  obtain ⟨k, hk⟩ := θs_torPt ht0 (by linarith) (α + t * b) (φ + t * d)
  obtain ⟨m, hm⟩ := φs_torPt ht0.le (by linarith) (α + t * b) (φ + t * d)
  rw [hk, hm, hρ.shift]
  rfl

/-! ## Lipschitz bound of the defect in the radial variable -/

/-- The defect `v_r − p_α v_α − p_φ v_φ` as a function of `(r, α, φ, p_α, p_φ)`. -/
def WfunV (V : Space → Space) (q : ℝ × ℝ × ℝ × ℝ × ℝ) : ℝ :=
  vRadV V q.1 q.2.1 q.2.2.1 - q.2.2.2.1 * vPolV V q.1 q.2.1 q.2.2.1 -
    q.2.2.2.2 * vTorV V q.1 q.2.1 q.2.2.1

/-- The compact convex box `r ∈ [r₁, r₂]`, `α, φ ∈ [−4, 4]`, `|p_α|, |p_φ| ≤ C`. -/
def WboxV (r₁ r₂ C : ℝ) : Set (ℝ × ℝ × ℝ × ℝ × ℝ) :=
  Icc r₁ r₂ ×ˢ Icc (-4) 4 ×ˢ Icc (-4) 4 ×ˢ Icc (-C) C ×ˢ Icc (-C) C

/-- The frame vector `e_R` is smooth in `φ`. -/
theorem contDiff_eRv (n : WithTop ℕ∞) : ContDiff ℝ n eRv := by
  refine contDiff_piLp 2 |>.mpr fun i => ?_
  fin_cases i <;> simp only [eRv, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
    PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;> fun_prop

/-- The frame vector `e_φ` is smooth in `φ`. -/
theorem contDiff_ePv (n : WithTop ℕ∞) : ContDiff ℝ n ePv := by
  refine contDiff_piLp 2 |>.mpr fun i => ?_
  fin_cases i <;> simp only [ePv, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
    PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;> fun_prop

/-- The toroidal point map is smooth. -/
theorem contDiff_torPt (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun q : ℝ × ℝ × ℝ × ℝ × ℝ => torPt q.1 q.2.1 q.2.2.1) := by
  refine contDiff_piLp 2 |>.mpr fun i => ?_
  fin_cases i <;> simp only [torPt, cylPt, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
    PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;> fun_prop

/-- `WfunV` is `C¹` on the box if `V` is `C¹` on an open set containing the shell. -/
theorem contDiffOn_WfunV {V : Space → Space} {U : Set Space} (hV : ContDiffOn ℝ 1 V U)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : r₂ < 1)
    (hU : ∀ r α φ, r₁ ≤ r → r ≤ r₂ → torPt r α φ ∈ U) (C : ℝ) :
    ContDiffOn ℝ 1 (WfunV V) (WboxV r₁ r₂ C) := by
  have hT : ContDiffOn ℝ 1 (fun q : ℝ × ℝ × ℝ × ℝ × ℝ => V (torPt q.1 q.2.1 q.2.2.1))
      (WboxV r₁ r₂ C) :=
    hV.comp (contDiff_torPt 1).contDiffOn fun q hq => hU _ _ _ hq.1.1 hq.1.2
  have hφ : ContDiff ℝ 1 (fun q : ℝ × ℝ × ℝ × ℝ × ℝ => q.2.2.1) := by fun_prop
  have h1 : ContDiffOn ℝ 1 (fun q : ℝ × ℝ × ℝ × ℝ × ℝ =>
      ⟪V (torPt q.1 q.2.1 q.2.2.1), eRv q.2.2.1⟫) (WboxV r₁ r₂ C) :=
    hT.inner ℝ ((contDiff_eRv 1).comp hφ).contDiffOn
  have h2 : ContDiffOn ℝ 1 (fun q : ℝ × ℝ × ℝ × ℝ × ℝ =>
      ⟪V (torPt q.1 q.2.1 q.2.2.1), ePv q.2.2.1⟫) (WboxV r₁ r₂ C) :=
    hT.inner ℝ ((contDiff_ePv 1).comp hφ).contDiffOn
  have h3 : ContDiffOn ℝ 1 (fun q : ℝ × ℝ × ℝ × ℝ × ℝ =>
      ⟪V (torPt q.1 q.2.1 q.2.2.1), eZv⟫) (WboxV r₁ r₂ C) :=
    hT.inner ℝ contDiffOn_const
  have hr : ∀ q ∈ WboxV r₁ r₂ C, q.1 ≠ 0 := fun q hq => by linarith [hq.1.1]
  have hR : ∀ q ∈ WboxV r₁ r₂ C, 1 + q.1 * cos q.2.1 ≠ 0 := fun q hq => by
    have := hq.1.2; have := hq.1.1
    nlinarith [neg_one_le_cos q.2.1, cos_le_one q.2.1]
  have hc : ContDiff ℝ 1 (fun q : ℝ × ℝ × ℝ × ℝ × ℝ => cos q.2.1) := by fun_prop
  have hs : ContDiff ℝ 1 (fun q : ℝ × ℝ × ℝ × ℝ × ℝ => sin q.2.1) := by fun_prop
  have hr1 : ContDiff ℝ 1 (fun q : ℝ × ℝ × ℝ × ℝ × ℝ => q.1) := by fun_prop
  have hpa : ContDiff ℝ 1 (fun q : ℝ × ℝ × ℝ × ℝ × ℝ => q.2.2.2.1) := by fun_prop
  have hpp : ContDiff ℝ 1 (fun q : ℝ × ℝ × ℝ × ℝ × ℝ => q.2.2.2.2) := by fun_prop
  have e : WfunV V = fun q => (cos q.2.1 * ⟪V (torPt q.1 q.2.1 q.2.2.1), eRv q.2.2.1⟫ +
      sin q.2.1 * ⟪V (torPt q.1 q.2.1 q.2.2.1), eZv⟫) -
      q.2.2.2.1 * ((cos q.2.1 * ⟪V (torPt q.1 q.2.1 q.2.2.1), eZv⟫ -
        sin q.2.1 * ⟪V (torPt q.1 q.2.1 q.2.2.1), eRv q.2.2.1⟫) / q.1) -
      q.2.2.2.2 * (⟪V (torPt q.1 q.2.1 q.2.2.1), ePv q.2.2.1⟫ / (1 + q.1 * cos q.2.1)) := rfl
  rw [e]
  refine ((hc.contDiffOn.mul h1).add (hs.contDiffOn.mul h3)).sub
    (hpa.contDiffOn.mul (((hc.contDiffOn.mul h3).sub (hs.contDiffOn.mul h1)).div
      hr1.contDiffOn hr)) |>.sub (hpp.contDiffOn.mul (h2.div ?_ hR))
  exact (contDiff_const.add (hr1.mul hc)).contDiffOn

/-- **Uniform Lipschitz bound in `r`** of the defect on the box. -/
theorem exists_lipschitz_WV {V : Space → Space} {U : Set Space} (hV : ContDiffOn ℝ 1 V U)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : r₂ < 1)
    (hU : ∀ r α φ, r₁ ≤ r → r ≤ r₂ → torPt r α φ ∈ U) (C : ℝ) :
    ∃ L : NNReal, ∀ q q' : ℝ × ℝ × ℝ × ℝ × ℝ, q ∈ WboxV r₁ r₂ C → q' ∈ WboxV r₁ r₂ C →
      q.2 = q'.2 → |WfunV V q - WfunV V q'| ≤ L * |q.1 - q'.1| := by
  have hconv : Convex ℝ (WboxV r₁ r₂ C) := by
    unfold WboxV
    exact (convex_Icc _ _).prod ((convex_Icc _ _).prod ((convex_Icc _ _).prod
      ((convex_Icc _ _).prod (convex_Icc _ _))))
  have hcpt : IsCompact (WboxV r₁ r₂ C) := by
    unfold WboxV
    exact isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod
      isCompact_Icc)))
  obtain ⟨L, hL⟩ := (contDiffOn_WfunV hV hr₁ hr₂ hU C).exists_lipschitzOnWith one_ne_zero hconv
    hcpt
  refine ⟨L, fun q q' hq hq' h2 => ?_⟩
  have h := hL.dist_le_mul q hq q' hq'
  rw [Real.dist_eq, Prod.dist_eq, h2, dist_self, Real.dist_eq,
    max_eq_left (abs_nonneg _)] at h
  exact h

/-! ## Flow tori -/

/-- **An exactly invariant torus of `V`** `(θ, φ) ↦ (R, z) = (Rk θ φ, zk θ φ)` with rotational
transform `ι`: `C²`, `2π`-periodic in `θ`, `π`-periodic in `φ`, solving the flow form
`c_T (∂_φ K + ι ∂_θ K) = (c_R, c_z)` of the field-line equations of `V` exactly (with `c_T ≠ 0`),
star-shaped about the axis in the flow angle, with positive winding rate and
`0 < ρmin ≤ rt ≤ ρmax < 1/2`. -/
structure FlowTorus (V : Space → Space) (ι ρmin ρmax : ℝ) (Rk zk : ℝ → ℝ → ℝ) : Prop where
  /-- `R` is `C²` in both angles. -/
  smooth_R : ContDiff ℝ 2 (fun p : ℝ × ℝ => Rk p.1 p.2)
  /-- `z` is `C²` in both angles. -/
  smooth_z : ContDiff ℝ 2 (fun p : ℝ × ℝ => zk p.1 p.2)
  /-- `R` is `2π`-periodic in `θ`. -/
  per_θ_R : ∀ θ φ, Rk (θ + 2 * π) φ = Rk θ φ
  /-- `z` is `2π`-periodic in `θ`. -/
  per_θ_z : ∀ θ φ, zk (θ + 2 * π) φ = zk θ φ
  /-- `R` is `π`-periodic in `φ`. -/
  per_φ_R : ∀ θ φ, Rk θ (φ + π) = Rk θ φ
  /-- `z` is `π`-periodic in `φ`. -/
  per_φ_z : ∀ θ φ, zk θ (φ + π) = zk θ φ
  /-- Exact invariance, `R`-component: `c_T (∂_φ R + ι ∂_θ R) = c_R`. -/
  inv_R : ∀ θ φ, cT V (Rk θ φ) φ (zk θ φ) *
      (deriv (fun φ' => Rk θ φ') φ + ι * deriv (fun θ' => Rk θ' φ) θ) = cR V (Rk θ φ) φ (zk θ φ)
  /-- Exact invariance, `z`-component: `c_T (∂_φ z + ι ∂_θ z) = c_z`. -/
  inv_z : ∀ θ φ, cT V (Rk θ φ) φ (zk θ φ) *
      (deriv (fun φ' => zk θ φ') φ + ι * deriv (fun θ' => zk θ' φ) θ) = cZ V (Rk θ φ) φ (zk θ φ)
  /-- The field is transverse to the poloidal planes on the torus. -/
  cT_ne : ∀ θ φ, cT V (Rk θ φ) φ (zk θ φ) ≠ 0
  /-- Star-shapedness in the flow angle. -/
  radial_pos : ∀ θ φ, 0 < (Rk θ φ - 1) * cos θ + zk θ φ * sin θ
  /-- Positive winding rate. -/
  wind_pos : ∀ θ φ, 0 < windK Rk zk θ φ
  /-- Lower radius bound. -/
  rt_ge : ∀ θ φ, ρmin ≤ rtK Rk zk θ φ
  /-- Upper radius bound. -/
  rt_le : ∀ θ φ, rtK Rk zk θ φ ≤ ρmax
  /-- `ρmin > 0`. -/
  ρmin_pos : 0 < ρmin
  /-- `ρmax < 1/2`. -/
  ρmax_lt : ρmax < 1 / 2

namespace FlowTorus

variable {V : Space → Space} {ι ρmin ρmax : ℝ} {Rk zk : ℝ → ℝ → ℝ}
  (hK : FlowTorus V ι ρmin ρmax Rk zk)
include hK

/-- `(R − 1)² + z² > 0`. -/
theorem rt2_pos (θ φ : ℝ) : 0 < (Rk θ φ - 1) ^ 2 + zk θ φ ^ 2 := by
  have h := (hK.ρmin_pos.trans_le (hK.rt_ge θ φ))
  rw [rtK] at h
  exact Real.sqrt_pos.mp h

/-- The radius is positive. -/
theorem rtK_pos (θ φ : ℝ) : 0 < rtK Rk zk θ φ := hK.ρmin_pos.trans_le (hK.rt_ge θ φ)

/-- `|R − 1| < 1/2`, in particular `R > 1/2`. -/
theorem R_gt (θ φ : ℝ) : 1 / 2 < Rk θ φ := by
  have h1 := hK.rt_le θ φ
  have h2 := hK.ρmax_lt
  have hsq : (Rk θ φ - 1) ^ 2 ≤ rtK Rk zk θ φ ^ 2 := by
    rw [rtK, Real.sq_sqrt (by positivity)]; nlinarith [sq_nonneg (zk θ φ)]
  have h0 := (hK.rtK_pos θ φ).le
  nlinarith

/-- The exact torus in polar form about the axis: `R − 1 = rt cos Θ`, `z = rt sin Θ`. -/
theorem polar (θ φ : ℝ) :
    Rk θ φ - 1 = rtK Rk zk θ φ * cos (Θf Rk zk θ φ) ∧
      zk θ φ = rtK Rk zk θ φ * sin (Θf Rk zk θ φ) :=
  angF_polar (hK.radial_pos θ φ)

/-- `R` is `C¹`. -/
theorem contDiff_R : ContDiff ℝ 1 (fun p : ℝ × ℝ => Rk p.1 p.2) := hK.smooth_R.of_le (by norm_num)

/-- `z` is `C¹`. -/
theorem contDiff_Z : ContDiff ℝ 1 (fun p : ℝ × ℝ => zk p.1 p.2) := hK.smooth_z.of_le (by norm_num)

/-- `R` is differentiable. -/
theorem differentiable_R : Differentiable ℝ (fun p : ℝ × ℝ => Rk p.1 p.2) :=
  hK.contDiff_R.differentiable (by norm_num)

/-- `z` is differentiable. -/
theorem differentiable_Z : Differentiable ℝ (fun p : ℝ × ℝ => zk p.1 p.2) :=
  hK.contDiff_Z.differentiable (by norm_num)

/-- The `θ`-partial derivative of `R`. -/
theorem hasDerivAt_R_θ (θ φ : ℝ) :
    HasDerivAt (fun θ' => Rk θ' φ) (deriv (fun θ' => Rk θ' φ) θ) θ := by
  have hd : DifferentiableAt ℝ ((fun p : ℝ × ℝ => Rk p.1 p.2) ∘ fun θ' => (θ', φ)) θ :=
    (hK.differentiable_R _).comp θ (by fun_prop)
  exact hd.hasDerivAt

/-- The `θ`-partial derivative of `z`. -/
theorem hasDerivAt_Z_θ (θ φ : ℝ) :
    HasDerivAt (fun θ' => zk θ' φ) (deriv (fun θ' => zk θ' φ) θ) θ := by
  have hd : DifferentiableAt ℝ ((fun p : ℝ × ℝ => zk p.1 p.2) ∘ fun θ' => (θ', φ)) θ :=
    (hK.differentiable_Z _).comp θ (by fun_prop)
  exact hd.hasDerivAt

/-- `∂_θ Θ = wind / rt²`. -/
theorem hasDerivAt_Θf_θ (θ φ : ℝ) :
    HasDerivAt (fun θ' => Θf Rk zk θ' φ) (windK Rk zk θ φ / rtK Rk zk θ φ ^ 2) θ := by
  have h := hasDerivAt_angF (θf := id) (af := fun θ' => Rk θ' φ - 1) (bf := fun θ' => zk θ' φ)
    (hasDerivAt_id θ) ((hK.hasDerivAt_R_θ θ φ).sub_const 1) (hK.hasDerivAt_Z_θ θ φ)
    (hK.radial_pos θ φ)
  rw [rtK, Real.sq_sqrt (by positivity), windK]
  exact h

/-- `∂_θ Θ > 0`. -/
theorem deriv_Θf_pos (θ φ : ℝ) : 0 < deriv (fun θ' => Θf Rk zk θ' φ) θ := by
  rw [(hK.hasDerivAt_Θf_θ θ φ).deriv]
  have := hK.wind_pos θ φ
  have := hK.rtK_pos θ φ
  positivity

/-- `Θ(θ + 2π, φ) = Θ(θ, φ) + 2π`. -/
theorem Θf_add_two_pi (θ φ : ℝ) : Θf Rk zk (θ + 2 * π) φ = Θf Rk zk θ φ + 2 * π := by
  simp only [Θf, angF, hK.per_θ_R, hK.per_θ_z, cos_add_two_pi, sin_add_two_pi]
  ring

/-- `Θ(θ, φ + π) = Θ(θ, φ)`. -/
theorem Θf_add_pi (θ φ : ℝ) : Θf Rk zk θ (φ + π) = Θf Rk zk θ φ := by
  simp only [Θf, hK.per_φ_R, hK.per_φ_z]

/-- `rt` of the torus is `2π`-periodic in `θ`. -/
theorem rtK_add_two_pi (θ φ : ℝ) : rtK Rk zk (θ + 2 * π) φ = rtK Rk zk θ φ := by
  simp only [rtK, hK.per_θ_R, hK.per_θ_z]

/-- `rt` of the torus is `π`-periodic in `φ`. -/
theorem rtK_add_pi (θ φ : ℝ) : rtK Rk zk θ (φ + π) = rtK Rk zk θ φ := by
  simp only [rtK, hK.per_φ_R, hK.per_φ_z]

/-- `Θ` is `C¹` on `ℝ²`. -/
theorem contDiff_Θf : ContDiff ℝ 1 (fun p : ℝ × ℝ => Θf Rk zk p.1 p.2) := by
  have hR := hK.contDiff_R
  have hZ := hK.contDiff_Z
  have hnum : ContDiff ℝ 1
      (fun p : ℝ × ℝ => zk p.1 p.2 * cos p.1 - (Rk p.1 p.2 - 1) * sin p.1) := by fun_prop
  have hden : ContDiff ℝ 1
      (fun p : ℝ × ℝ => (Rk p.1 p.2 - 1) * cos p.1 + zk p.1 p.2 * sin p.1) := by fun_prop
  exact contDiff_fst.add (Real.contDiff_arctan.comp
    (hnum.div hden fun p => (hK.radial_pos p.1 p.2).ne'))

/-- `Φ` is `C¹`. -/
theorem contDiff_Φmap : ContDiff ℝ 1 (Φmap Rk zk) := hK.contDiff_Θf.prodMk contDiff_snd

/-- `dΦ` is the derivative of `Φ`. -/
theorem hasFDerivAt_Φmap (p : ℝ × ℝ) : HasFDerivAt (Φmap Rk zk) (dΦ Rk zk p) p :=
  ((hK.contDiff_Θf.differentiable (by norm_num) p).hasFDerivAt).prodMk (hasFDerivAt_snd)

/-- `DΘ · (1, 0) = ∂_θ Θ = wind / rt²`. -/
theorem fderiv_Θf_one_zero (p : ℝ × ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ => Θf Rk zk p.1 p.2) p (1, 0) =
      windK Rk zk p.1 p.2 / rtK Rk zk p.1 p.2 ^ 2 := by
  have hD := (hK.contDiff_Θf.differentiable (by norm_num) p).hasFDerivAt
  have h := hD.comp_hasDerivAt_of_eq p.1
    (HasDerivAt.prodMk (hasDerivAt_id p.1) (hasDerivAt_const p.1 p.2)) rfl
  exact h.unique (hK.hasDerivAt_Θf_θ p.1 p.2)

/-- `dΦ` is injective. -/
theorem dΦ_injective (p : ℝ × ℝ) : Function.Injective (dΦ Rk zk p) := by
  refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
  have h2 : v.2 = 0 := by simpa [dΦ] using congrArg Prod.snd hv
  have h1 : fderiv ℝ (fun p : ℝ × ℝ => Θf Rk zk p.1 p.2) p v = 0 := by
    simpa [dΦ] using congrArg Prod.fst hv
  have hv' : v = v.1 • ((1 : ℝ), (0 : ℝ)) := by ext <;> simp [h2]
  rw [hv', map_smul, fderiv_Θf_one_zero hK, smul_eq_mul] at h1
  have hpos : 0 < windK Rk zk p.1 p.2 / rtK Rk zk p.1 p.2 ^ 2 := by
    have := hK.wind_pos p.1 p.2
    have := hK.rtK_pos p.1 p.2
    positivity
  have hv1 : v.1 = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hpos.ne'
  exact Prod.ext hv1 h2

/-- The derivative of `Φ` as a continuous linear equivalence. -/
def dΦequiv (p : ℝ × ℝ) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  (LinearEquiv.ofInjectiveEndo (dΦ Rk zk p).toLinearMap (hK.dΦ_injective p)).toContinuousLinearEquiv

/-- `Φ` has the invertible strict derivative `dΦequiv` everywhere. -/
theorem hasStrictFDerivAt_Φmap (p : ℝ × ℝ) :
    HasStrictFDerivAt (Φmap Rk zk) (hK.dΦequiv p : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := by
  have h := (hK.contDiff_Φmap.contDiffAt (x := p)).hasStrictFDerivAt (by norm_num)
  rw [(hK.hasFDerivAt_Φmap p).fderiv] at h
  have e : (hK.dΦequiv p : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = dΦ Rk zk p :=
    ContinuousLinearMap.ext fun v => rfl
  rw [e]; exact h

/-- `Φ` is a bijection of `ℝ²`. -/
theorem Φmap_bijective : Function.Bijective (Φmap Rk zk) := by
  constructor
  · intro p q hpq
    simp only [Φmap, Prod.mk.injEq] at hpq
    obtain ⟨h1, h2⟩ := hpq
    have hmono : StrictMono (fun θ => Θf Rk zk θ p.2) :=
      strictMono_of_deriv_pos (fun θ => hK.deriv_Θf_pos θ p.2)
    rw [← h2] at h1
    exact Prod.ext (hmono.injective h1) h2
  · intro q
    have hcont : Continuous (fun θ => Θf Rk zk θ q.2) :=
      continuous_iff_continuousAt.2 fun θ => (hK.hasDerivAt_Θf_θ θ q.2).continuousAt
    have hb : ∀ θ, |Θf Rk zk θ q.2 - θ| < π / 2 := fun θ => angF_sub_mem _ _ _
    have htop : Tendsto (fun θ => Θf Rk zk θ q.2) atTop atTop :=
      tendsto_atTop_mono (fun θ => by simp only [id]; linarith [(abs_lt.mp (hb θ)).1])
        (tendsto_atTop_add_const_right _ (-(π / 2)) tendsto_id)
    have hbot : Tendsto (fun θ => Θf Rk zk θ q.2) atBot atBot :=
      tendsto_atBot_mono (fun θ => by simp only [id]; linarith [(abs_lt.mp (hb θ)).2])
        (tendsto_atBot_add_const_right _ (π / 2) tendsto_id)
    obtain ⟨θ, hθ⟩ := hcont.surjective htop hbot q.1
    exact ⟨(θ, q.2), by simp [Φmap, hθ]⟩

/-- `Φ` as a homeomorphism of `ℝ²`. -/
def homeo : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  (Equiv.ofBijective (Φmap Rk zk) hK.Φmap_bijective).toHomeomorphOfContinuousOpen
    hK.contDiff_Φmap.continuous
    (isOpenMap_of_hasStrictFDerivAt_equiv (f' := hK.dΦequiv) hK.hasStrictFDerivAt_Φmap)

/-- The homeomorphism is `Φ`. -/
theorem coe_homeo : ⇑hK.homeo = Φmap Rk zk := rfl

/-- `Φ ∘ Φ⁻¹ = id`. -/
theorem Φmap_symm (q : ℝ × ℝ) : Φmap Rk zk (hK.homeo.symm q) = q := by
  rw [← hK.coe_homeo]; exact hK.homeo.apply_symm_apply q

/-- `Φ⁻¹ ∘ Φ = id`. -/
theorem symm_Φmap (p : ℝ × ℝ) : hK.homeo.symm (Φmap Rk zk p) = p := by
  rw [← hK.coe_homeo]; exact hK.homeo.symm_apply_apply p

/-- `Φ⁻¹` preserves the toroidal angle. -/
theorem symm_snd (α φ : ℝ) : (hK.homeo.symm (α, φ)).2 = φ := by
  have := congrArg Prod.snd (hK.Φmap_symm (α, φ)); exact this

/-- `Θ(Φ⁻¹(α, φ)) = α`. -/
theorem Θf_symm (α φ : ℝ) : Θf Rk zk (hK.homeo.symm (α, φ)).1 φ = α := by
  have h1 := congrArg Prod.fst (hK.Φmap_symm (α, φ))
  simp only [Φmap] at h1
  rw [hK.symm_snd α φ] at h1
  exact h1

/-- `Φ⁻¹` is `C¹` (inverse function theorem). -/
theorem contDiff_symm : ContDiff ℝ 1 hK.homeo.symm :=
  hK.homeo.contDiff_symm (f₀' := hK.dΦequiv) (fun a => (hK.hasStrictFDerivAt_Φmap a).hasFDerivAt)
    hK.contDiff_Φmap

/-- **The profile of the torus**: `ρ(α, φ) = rt(K(Φ⁻¹(α, φ)))`. -/
def profile (α φ : ℝ) : ℝ := rtK Rk zk (hK.homeo.symm (α, φ)).1 (hK.homeo.symm (α, φ)).2

/-- `ρ(Θ(θ, φ), φ) = rt(K(θ, φ))`. -/
theorem profile_Θf (θ φ : ℝ) : hK.profile (Θf Rk zk θ φ) φ = rtK Rk zk θ φ := by
  rw [profile, show ((Θf Rk zk θ φ, φ) : ℝ × ℝ) = Φmap Rk zk (θ, φ) from rfl, symm_Φmap]

/-- `rt` of the torus is `C¹`. -/
theorem contDiff_rtK : ContDiff ℝ 1 (fun p : ℝ × ℝ => rtK Rk zk p.1 p.2) := by
  have hR := hK.contDiff_R
  have hZ := hK.contDiff_Z
  have h : ContDiff ℝ 1 (fun p : ℝ × ℝ => (Rk p.1 p.2 - 1) ^ 2 + zk p.1 p.2 ^ 2) := by fun_prop
  exact h.sqrt fun p => (hK.rt2_pos p.1 p.2).ne'

/-- The profile is `C¹`. -/
theorem contDiff_profile : ContDiff ℝ 1 (fun p : ℝ × ℝ => hK.profile p.1 p.2) :=
  hK.contDiff_rtK.comp hK.contDiff_symm

/-- `ρ` is `2π`-periodic in the poloidal angle. -/
theorem profile_add_two_pi (α φ : ℝ) : hK.profile (α + 2 * π) φ = hK.profile α φ := by
  have h : Φmap Rk zk ((hK.homeo.symm (α, φ)).1 + 2 * π, (hK.homeo.symm (α, φ)).2) =
      (α + 2 * π, φ) := by
    simp only [Φmap, hK.Θf_add_two_pi, hK.symm_snd, hK.Θf_symm]
  rw [profile, ← h, symm_Φmap, hK.rtK_add_two_pi]
  rfl

/-- `ρ` is `π`-periodic in the toroidal angle. -/
theorem profile_add_pi (α φ : ℝ) : hK.profile α (φ + π) = hK.profile α φ := by
  have h : Φmap Rk zk ((hK.homeo.symm (α, φ)).1, (hK.homeo.symm (α, φ)).2 + π) =
      (α, φ + π) := by
    simp only [Φmap, hK.Θf_add_pi, hK.symm_snd, hK.Θf_symm]
  rw [profile, ← h, symm_Φmap, hK.rtK_add_pi]
  rfl

/-- **The profile is a torus profile.** -/
theorem torusProfile : TorusProfile hK.profile where
  differentiable := hK.contDiff_profile.differentiable (by norm_num)
  periodic_left := hK.profile_add_two_pi
  periodic_right := fun α φ => by
    rw [show φ + 2 * π = (φ + π) + π by ring, hK.profile_add_pi, hK.profile_add_pi]

/-- `ρmin ≤ ρ ≤ ρmax`. -/
theorem profile_bounds (α φ : ℝ) : ρmin ≤ hK.profile α φ ∧ hK.profile α φ ≤ ρmax :=
  ⟨hK.rt_ge _ _, hK.rt_le _ _⟩

/-- **Tangency.** On the torus `r = ρ(α, φ)` the toroidal components of `V` satisfy
`v_r = Dρ(α, φ) · (v_α, v_φ)`. -/
theorem tangent (α φ : ℝ) :
    vRadV V (hK.profile α φ) α φ =
      fderiv ℝ (fun p : ℝ × ℝ => hK.profile p.1 p.2) (α, φ)
        (vPolV V (hK.profile α φ) α φ, vTorV V (hK.profile α φ) α φ) := by
  set θ := (hK.homeo.symm (α, φ)).1
  have hΘ : Θf Rk zk θ φ = α := hK.Θf_symm α φ
  have hr0 : hK.profile α φ = rtK Rk zk θ φ := by rw [← hK.profile_Θf θ φ, hΘ]
  obtain ⟨hpa, hpb⟩ := hK.polar θ φ
  rw [hΘ] at hpa hpb
  have hrpos := hK.rtK_pos θ φ
  have hr2 : rtK Rk zk θ φ ^ 2 = (Rk θ φ - 1) ^ 2 + zk θ φ ^ 2 :=
    Real.sq_sqrt (hK.rt2_pos θ φ).le
  -- derivatives along the invariant line `t ↦ (θ + ι t, φ + t)`
  have hLR := hasDerivAt_line hK.differentiable_R θ φ ι 1
  have hLZ := hasDerivAt_line hK.differentiable_Z θ φ ι 1
  set La := ι * deriv (fun θ' => Rk θ' φ) θ + 1 * deriv (fun φ' => Rk θ φ') φ with hLa
  set Lb := ι * deriv (fun θ' => zk θ' φ) θ + 1 * deriv (fun φ' => zk θ φ') φ with hLb
  have hpos0 : 0 < (Rk (θ + 0 * ι) (φ + 0 * 1) - 1) * cos (θ + 0 * ι) +
      zk (θ + 0 * ι) (φ + 0 * 1) * sin (θ + 0 * ι) := by
    simpa using hK.radial_pos θ φ
  have hΘl := hasDerivAt_angF (hasDerivAt_affine θ ι) (hLR.sub_const 1) hLZ hpos0
  simp only [zero_mul, add_zero] at hΘl
  set LΘ := ((Rk θ φ - 1) * Lb - zk θ φ * La) / ((Rk θ φ - 1) ^ 2 + zk θ φ ^ 2) with hLΘ
  -- the identity `ρ(Θ, φ) = rt(K)` along the line
  set D := fderiv ℝ (fun p : ℝ × ℝ => hK.profile p.1 p.2) (α, φ)
  have hD : HasFDerivAt (fun p : ℝ × ℝ => hK.profile p.1 p.2) D (α, φ) :=
    (hK.contDiff_profile.differentiable (by norm_num) _).hasFDerivAt
  have hc : HasDerivAt (fun t : ℝ => (Θf Rk zk (θ + t * ι) (φ + t * 1), φ + t * 1))
      (LΘ, 1) 0 := HasDerivAt.prodMk hΘl (hasDerivAt_affine φ 1)
  have h1 := hD.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp [hΘ])
  have hfun : ((fun p : ℝ × ℝ => hK.profile p.1 p.2) ∘
      fun t : ℝ => (Θf Rk zk (θ + t * ι) (φ + t * 1), φ + t * 1)) =
      fun t => rtK Rk zk (θ + t * ι) (φ + t * 1) :=
    funext fun t => hK.profile_Θf _ _
  rw [hfun] at h1
  have hf := ((hLR.sub_const 1).pow 2).add (hLZ.pow 2)
  have hs := hf.sqrt (ne_of_gt (by
    simp only [Pi.add_apply, Pi.pow_apply, zero_mul, add_zero]
    exact hK.rt2_pos θ φ))
  have hkey := h1.unique hs
  simp only [Pi.add_apply, Pi.pow_apply, zero_mul, add_zero, Nat.cast_ofNat] at hkey
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, pow_one] at hkey
  -- the invariance equations
  have hT := hK.cT_ne θ φ
  have hIR : cT V (Rk θ φ) φ (zk θ φ) * La = cR V (Rk θ φ) φ (zk θ φ) := by
    rw [hLa, ← hK.inv_R θ φ]; ring
  have hIZ : cT V (Rk θ φ) φ (zk θ φ) * Lb = cZ V (Rk θ φ) φ (zk θ φ) := by
    rw [hLb, ← hK.inv_z θ φ]; ring
  -- algebra
  have hR1 : 1 + rtK Rk zk θ φ * cos α = Rk θ φ := by linarith
  have hZ1 : rtK Rk zk θ φ * sin α = zk θ φ := by linarith
  have hcα : cos α = (Rk θ φ - 1) / rtK Rk zk θ φ := by field_simp; linarith
  have hsα : sin α = zk θ φ / rtK Rk zk θ φ := by field_simp; linarith
  have hvec : ((vPolV V (rtK Rk zk θ φ) α φ, vTorV V (rtK Rk zk θ φ) α φ) : ℝ × ℝ) =
      vTorV V (rtK Rk zk θ φ) α φ • (LΘ, (1 : ℝ)) := by
    ext
    · simp only [Prod.smul_mk, smul_eq_mul, vPolV, vTorV, hR1, hZ1, hLΘ]
      rw [hcα, hsα, ← hr2, ← hIR, ← hIZ]
      field_simp
    · simp
  rw [hr0, hvec, map_smul, smul_eq_mul, hkey]
  simp only [vRadV, vTorV, hR1, hZ1]
  rw [hcα, hsα, ← hIR, ← hIZ, show √((Rk θ φ - 1) ^ 2 + zk θ φ ^ 2) = rtK Rk zk θ φ from rfl]
  field_simp

/-- The derivative of the profile is bounded (it is continuous and doubly periodic). -/
theorem exists_bound_fderiv_profile :
    ∃ C, ∀ p, ‖fderiv ℝ (fun p : ℝ × ℝ => hK.profile p.1 p.2) p‖ ≤ C := by
  set F := fun p : ℝ × ℝ => hK.profile p.1 p.2
  have hcont : Continuous (fderiv ℝ F) := hK.contDiff_profile.continuous_fderiv (by norm_num)
  have hper : ∀ v : ℝ × ℝ, (fun x => F (x + v)) = F → ∀ x, fderiv ℝ F (x + v) = fderiv ℝ F x :=
    fun v hv x => by rw [← fderiv_comp_add_right (𝕜 := ℝ) (f := F) (x := x) v, hv]
  refine exists_bound_of_periodic hcont (fun a b => ?_) (fun a b => ?_)
  · have h := hper ((2 * π, 0) : ℝ × ℝ) (funext fun x => by
      simp only [F, Prod.fst_add, Prod.snd_add, add_zero, hK.profile_add_two_pi]) (a, b)
    simpa using h
  · have h := hper ((0, 2 * π) : ℝ × ℝ) (funext fun x => by
      simp only [F, Prod.fst_add, Prod.snd_add, add_zero, hK.torusProfile.periodic_right]) (a, b)
    simpa using h

/-- **Grönwall bound on the collar**: if `V` is `C¹` on a set containing the shell
`ρmin − g₀ ≤ rt ≤ ρmax + g₀`, then with `G = rt − ρ(θs, φs)`, `|DG · V| ≤ L |G|` wherever
`0 < rt < 1/2` and `|G| < g₀`. -/
theorem exists_gronwall {U : Set Space} (hV : ContDiffOn ℝ 1 V U) {g₀ : ℝ} (hg₀ : g₀ < ρmin)
    (hU : ∀ r α φ, ρmin - g₀ ≤ r → r ≤ ρmax + g₀ → torPt r α φ ∈ U) :
    ∃ L : ℝ, ∀ y : Space, rt y < 1 / 2 → 0 < rt y →
      |rt y - hK.profile (θs y) (φs y)| < g₀ →
      |fderiv ℝ (fun x => rt x - hK.profile (θs x) (φs x)) y (V y)| ≤
        L * |rt y - hK.profile (θs y) (φs y)| := by
  obtain ⟨Cρ, hCρ⟩ := hK.exists_bound_fderiv_profile
  have hmax := hK.ρmax_lt
  have hmin := hK.ρmin_pos
  have hρle : ρmin ≤ ρmax := (hK.rt_ge 0 0).trans (hK.rt_le 0 0)
  obtain ⟨L, hL⟩ := exists_lipschitz_WV hV (r₁ := ρmin - g₀) (r₂ := ρmax + g₀) (by linarith)
    (by linarith) hU Cρ
  have hρ := hK.torusProfile
  refine ⟨L, fun y hy hpos hG => ?_⟩
  have hyeq : y = torPt (rt y) (θs y) (φs y) := eq_torPt hy
  obtain ⟨hr0l, hr0u⟩ := hK.profile_bounds (θs y) (φs y)
  have hrr := abs_lt.mp hG
  have hF := fderiv_G_V_torPt V hρ hpos hy (θs y) (φs y)
  rw [← hyeq] at hF
  rw [hF]
  have htan := hK.tangent (θs y) (φs y)
  set D := fderiv ℝ (fun p : ℝ × ℝ => hK.profile p.1 p.2) (θs y, φs y) with hDdef
  have hlin : ∀ x x' : ℝ, D (x, x') = x * D (1, 0) + x' * D (0, 1) := fun x x' => by
    rw [show ((x, x') : ℝ × ℝ) = x • ((1 : ℝ), (0 : ℝ)) + x' • ((0 : ℝ), (1 : ℝ)) by simp,
      map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hb1 : |D (1, 0)| ≤ Cρ := by
    have := D.le_opNorm (1, 0)
    rw [Real.norm_eq_abs] at this
    simpa using this.trans (by simpa using hCρ (θs y, φs y))
  have hb2 : |D (0, 1)| ≤ Cρ := by
    have := D.le_opNorm (0, 1)
    rw [Real.norm_eq_abs] at this
    simpa using this.trans (by simpa using hCρ (θs y, φs y))
  set r₀ := hK.profile (θs y) (φs y)
  set q : ℝ × ℝ × ℝ × ℝ × ℝ := (rt y, θs y, φs y, D (1, 0), D (0, 1))
  set q₀ : ℝ × ℝ × ℝ × ℝ × ℝ := (r₀, θs y, φs y, D (1, 0), D (0, 1))
  have hWq : vRadV V (rt y) (θs y) (φs y) -
      D (vPolV V (rt y) (θs y) (φs y), vTorV V (rt y) (θs y) (φs y)) = WfunV V q := by
    rw [hlin]; simp only [WfunV, q]; ring
  have hWq₀ : WfunV V q₀ = 0 := by
    simp only [WfunV, q₀]; rw [htan, hlin]; ring
  have hang : ∀ w : ℂ, Complex.arg w ∈ Icc (-4 : ℝ) 4 := fun w =>
    ⟨by linarith [Complex.neg_pi_lt_arg w, Real.pi_le_four],
      by linarith [Complex.arg_le_pi w, Real.pi_le_four]⟩
  have hmem : ∀ x : ℝ, ρmin - g₀ ≤ x → x ≤ ρmax + g₀ →
      (x, θs y, φs y, D (1, 0), D (0, 1)) ∈ WboxV (ρmin - g₀) (ρmax + g₀) Cρ := fun x h1 h2 =>
    ⟨⟨h1, h2⟩, hang _, hang _, abs_le.mp hb1, abs_le.mp hb2⟩
  have hq : q ∈ WboxV (ρmin - g₀) (ρmax + g₀) Cρ := hmem _ (by linarith) (by linarith)
  have hq₀ : q₀ ∈ WboxV (ρmin - g₀) (ρmax + g₀) Cρ := hmem _ (by linarith) (by linarith)
  rw [hWq, ← sub_zero (WfunV V q), ← hWq₀]
  exact hL q q₀ hq hq₀ rfl

end FlowTorus

/-- The closed tube `{rt ≤ R₁}` about the magnetic axis is compact. -/
theorem isCompact_rtLe' {R₁ : ℝ} (hR₁ : R₁ < 1 / 2) : IsCompact {x : Space | rt x ≤ R₁} := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_le continuous_rt continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Space)) (r := 2)).subset fun y hy => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  have hy' : rt y ≤ R₁ := hy
  have hn : ‖y‖ ^ 2 = r2 y + y 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]; rfl
  have hr2 : 0 ≤ r2 y := by unfold r2; positivity
  have hRc : Rc y ^ 2 = r2 y := Real.sq_sqrt hr2
  have hRc0 : 0 ≤ Rc y := Real.sqrt_nonneg _
  have hsq := rt_sq y
  have h0 := rt_nonneg y
  have hrt2 : rt y ^ 2 ≤ (1 / 2) ^ 2 := by nlinarith
  have hz : y 2 ^ 2 ≤ (1 / 2) ^ 2 := by nlinarith [sq_nonneg (Rc y - 1)]
  have hR1 : (Rc y - 1) ^ 2 ≤ (1 / 2) ^ 2 := by nlinarith [sq_nonneg (y 2)]
  have hR2 : Rc y ≤ 3 / 2 := by nlinarith
  have hN : ‖y‖ ^ 2 ≤ 2 ^ 2 := by rw [hn, ← hRc]; nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg y) (by norm_num) two_ne_zero).mp hN

namespace FlowTorus

variable {V : Space → Space} {ι ρmin ρmax : ℝ} {Rk zk : ℝ → ℝ → ℝ}
  (hK : FlowTorus V ι ρmin ρmax Rk zk)
include hK

/-- **All-time confinement, existence and uniqueness of field lines from a flow torus.** Let `V`
be `C¹` on an open set `U` containing the closed tube `rt ≤ R₁` (`ρmax + g₀ ≤ R₁ < 1/2`,
`0 < g₀ < ρmin`). Then from every point on the magnetic axis or inside the torus
`rt < ρ(θs, φs)` (`ρ` the profile) there is exactly one two-sided field line of `V` through it at
parameter `0`, and every field line of `V` starting there stays inside the torus, within distance
`ρmax` of the axis, for all time. -/
theorem confined_existsUnique {U : Set Space} (hUo : IsOpen U) (hV : ContDiffOn ℝ 1 V U)
    {R₁ g₀ : ℝ} (hR₁ : R₁ < 1 / 2) (hg₀ : 0 < g₀) (hg : g₀ < ρmin) (hgR : ρmax + g₀ ≤ R₁)
    (hKU : ∀ y, rt y ≤ R₁ → y ∈ U) :
    (∀ x₀ : Space, (rt x₀ = 0 ∨ rt x₀ < hK.profile (θs x₀) (φs x₀)) →
      ∃! γ : ℝ → Space, IsFieldLine V γ ∧ γ 0 = x₀) ∧
    ∀ γ : ℝ → Space, IsFieldLine V γ →
      (rt (γ 0) = 0 ∨ rt (γ 0) < hK.profile (θs (γ 0)) (φs (γ 0))) → ∀ t, rt (γ t) ≤ ρmax ∧
        (rt (γ t) = 0 ∨ rt (γ t) < hK.profile (θs (γ t)) (φs (γ t))) := by
  have hmin := hK.ρmin_pos
  have hU : ∀ r α φ, ρmin - g₀ ≤ r → r ≤ ρmax + g₀ → torPt r α φ ∈ U := fun r α φ h1 h2 =>
    hKU _ (by rw [rt_torPt (by linarith) (by linarith)]; linarith)
  obtain ⟨L, hL⟩ := hK.exists_gronwall hV hg hU
  have hρ := hK.torusProfile
  have hlo : ∀ a b, ρmin ≤ hK.profile a b := fun a b => (hK.profile_bounds a b).1
  have hhi : ∀ a b, hK.profile a b ≤ ρmax := fun a b => (hK.profile_bounds a b).2
  have hmaxlt := hK.ρmax_lt
  have hρle : ρmin ≤ ρmax := (hlo 0 0).trans (hhi 0 0)
  have hinv : ODEGlobal.LocallyInvariant V (tube.inside hK.profile) :=
    fun a b α ha hb h0 hα => torus_trapping_Icc (c := tube) (B := V) hρ
      (ρmin := ρmin) (R₁ := ρmax) (g₀ := g₀) (L := L) hmin hlo hhi
      (isClosed_subTube hmaxlt) hg₀ (fun x hx hr hG => hL x hx hr hG) ha hb hα h0
  have hΩK : tube.inside hK.profile ⊆ {x : Space | rt x ≤ R₁} := fun x hx =>
    ((TubeCoords.inside_subset_closedTube (by linarith) hhi hx).2).trans (by linarith)
  have hstay : ∀ x₀, (rt x₀ = 0 ∨ rt x₀ < hK.profile (θs x₀) (φs x₀)) →
      x₀ ∈ tube.inside hK.profile := fun x₀ hx₀ => by
    rcases hx₀ with h | h
    · exact ⟨show rt x₀ < 1 / 2 by linarith, Or.inl h.le⟩
    · exact ⟨show rt x₀ < 1 / 2 by linarith [hhi (θs x₀) (φs x₀)], Or.inr h⟩
  have hglob := fun x₀ (hx₀ : x₀ ∈ tube.inside hK.profile) =>
    ODEGlobal.existsUnique_global hUo hV (isCompact_rtLe' hR₁) (fun y hy => hKU y hy) hΩK hinv hx₀
  refine ⟨fun x₀ hx₀ => ?_, fun γ hγ h0 t => ?_⟩
  · obtain ⟨⟨γ, ⟨hγ0, hγ⟩, huniq⟩, -⟩ := hglob x₀ (hstay x₀ hx₀)
    exact ⟨γ, ⟨hγ, hγ0⟩, fun γ' ⟨h', h0'⟩ => huniq γ' ⟨h0', h'⟩⟩
  · obtain ⟨-, hst⟩ := hglob (γ 0) (hstay _ h0)
    have ht := hst γ rfl hγ t
    refine ⟨(TubeCoords.inside_subset_closedTube (by linarith) hhi ht).2, ?_⟩
    rcases ht.2 with h | h
    · exact Or.inl (le_antisymm h (rt_nonneg _))
    · exact Or.inr h

end FlowTorus

end PlasmaLean.Design.RationalStellaratorGC
