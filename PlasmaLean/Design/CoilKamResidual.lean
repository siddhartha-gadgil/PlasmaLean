/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.CoilKamLip
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The complexified flow-form residual of a rational coil torus

Stage 2 of the coil-field KAM (`notes/theory/coil-kam-status.md`). For a rational torus
(`TRec` records at scale `D`) the flow-form residuals are holomorphic functions of the complex
angles `(θ, ψ)` (`ψ = φ` the geometric toroidal angle):

`resCR θ ψ = (−sin ψ F₀ + cos ψ F₁)·𝓛R − R·(cos ψ F₀ + sin ψ F₁)`,
`resCZ θ ψ = (−sin ψ F₀ + cos ψ F₁)·𝓛z − R·F₂`,

`F = coilFieldCC (torusMapC uR uZ θ ψ 0 0)`, `R, 𝓛R, 𝓛z` the complex Fourier sums. This file
proves the hypotheses of `PaleyWiener.Bd_of_samples` for them:

* `resCR_ofReal`, `resCZ_ofReal`: at real points with the torus point in `realTube w`
  (`w < 7/20`) they are the real residuals `resR`, `resZ` of `Design/CoilKamTorus`;
* `resCR_add_two_pi_left/right` (and `Z`): biperiodicity;
* `resCR_differentiableOn`, `resCZ_differentiableOn`: joint holomorphy on
  `stripC ρ' ×ˢ stripC ρ'` provided the complexified torus maps the strip into the coil
  neighbourhood `coilNbhdP w η` (`hmap`);
* `norm_resCR_le`, `norm_resCZ_le`: sup bounds on the closed strip from `Mcoil` and the
  coefficient sums;
* `torus_hmap`: the mapping hypothesis from explicit numerical bounds (real torus in a tube,
  coefficient sums at the strip weight, `cosh`, `sinh` bounds), using the exact identities
  `norm_imV_cylC_sq`, `norm_reV_cylC_sub_sq`.

**Sanity.** `norm_sin_ofReal_le` (the bound `norm_sin_le_cosh` at real points is `≤ 1`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.CoilKam

open Complex Set PlasmaLean.Theory.KAM PlasmaLean.Theory.KAM.PaleyWiener
  PlasmaLean.Theory.KAM.FourierSumHolo PlasmaLean.Fields PlasmaLean.Fields.BiotSavartComplex
  PlasmaLean.Design.CoilFieldComplex PlasmaLean.Design.PolygonCoil
  PlasmaLean.Design.RationalStellarator.CoilsTF

/-- The complexified torus point `cyl(R, ψ, z)`. -/
def torusC (D : ℕ) (recs : List TRec) (θ ψ : ℂ) : CVec := torusMapC (uR D recs) (uZ D recs) θ ψ 0 0

/-- **The complexified residual** `E_R`. -/
def resCR (D : ℕ) (ι : ℝ) (recs : List TRec) (θ ψ : ℂ) : ℂ :=
  let F := coilFieldCC (torusC D recs θ ψ)
  (-Complex.sin ψ * F 0 + Complex.cos ψ * F 1) * fourierSumC (uLR D ι recs) θ ψ -
    fourierSumC (uR D recs) θ ψ * (Complex.cos ψ * F 0 + Complex.sin ψ * F 1)

/-- **The complexified residual** `E_z`. -/
def resCZ (D : ℕ) (ι : ℝ) (recs : List TRec) (θ ψ : ℂ) : ℂ :=
  let F := coilFieldCC (torusC D recs θ ψ)
  (-Complex.sin ψ * F 0 + Complex.cos ψ * F 1) * fourierSumC (uLZ D ι recs) θ ψ -
    fourierSumC (uR D recs) θ ψ * F 2

/-! ## Real points -/

theorem torusC_ofReal (D : ℕ) (recs : List TRec) (θ ψ : ℝ) :
    torusC D recs θ ψ = ofRealV (torusPt D recs θ ψ) := by
  unfold torusC torusMapC torusPt
  rw [fourierSumC_uR_ofReal, fourierSumC_uZ_ofReal, add_zero, add_zero, cylC_ofReal]

theorem resCR_ofReal {D : ℕ} {ι : ℝ} {recs : List TRec} {w : ℝ} (hw : w < 7 / 20) {θ ψ : ℝ}
    (hT : torusPt D recs θ ψ ∈ realTube w) :
    resCR D ι recs θ ψ = (resR D ι recs θ ψ : ℂ) := by
  unfold resCR resR
  simp only
  rw [torusC_ofReal, coilFieldCC_ofReal hw hT, fourierSumC_uLR_ofReal, fourierSumC_uR_ofReal]
  simp only [ofRealV, Bc, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
  push_cast; ring

theorem resCZ_ofReal {D : ℕ} {ι : ℝ} {recs : List TRec} {w : ℝ} (hw : w < 7 / 20) {θ ψ : ℝ}
    (hT : torusPt D recs θ ψ ∈ realTube w) :
    resCZ D ι recs θ ψ = (resZ D ι recs θ ψ : ℂ) := by
  unfold resCZ resZ
  simp only
  rw [torusC_ofReal, coilFieldCC_ofReal hw hT, fourierSumC_uLZ_ofReal, fourierSumC_uR_ofReal]
  simp only [ofRealV, Bc, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
  push_cast; ring

/-! ## Periodicity -/

theorem torusC_add_two_pi_left (D : ℕ) (recs : List TRec) (θ ψ : ℂ) :
    torusC D recs (θ + 2 * Real.pi) ψ = torusC D recs θ ψ := torusMapC_add_two_pi_left _ _ _ _ _ _

theorem torusC_add_two_pi_right (D : ℕ) (recs : List TRec) (θ ψ : ℂ) :
    torusC D recs θ (ψ + 2 * Real.pi) = torusC D recs θ ψ := torusMapC_add_two_pi_right _ _ _ _ _ _

theorem resCR_add_two_pi_left (D : ℕ) (ι : ℝ) (recs : List TRec) (θ ψ : ℂ) :
    resCR D ι recs (θ + 2 * Real.pi) ψ = resCR D ι recs θ ψ := by
  simp only [resCR, torusC_add_two_pi_left, fourierSumC_add_two_pi_left]

theorem resCZ_add_two_pi_left (D : ℕ) (ι : ℝ) (recs : List TRec) (θ ψ : ℂ) :
    resCZ D ι recs (θ + 2 * Real.pi) ψ = resCZ D ι recs θ ψ := by
  simp only [resCZ, torusC_add_two_pi_left, fourierSumC_add_two_pi_left]

theorem sin_cos_add_two_pi (ψ : ℂ) :
    Complex.sin (ψ + 2 * Real.pi) = Complex.sin ψ ∧ Complex.cos (ψ + 2 * Real.pi) = Complex.cos ψ :=
  ⟨Complex.sin_periodic ψ, Complex.cos_periodic ψ⟩

theorem resCR_add_two_pi_right (D : ℕ) (ι : ℝ) (recs : List TRec) (θ ψ : ℂ) :
    resCR D ι recs θ (ψ + 2 * Real.pi) = resCR D ι recs θ ψ := by
  simp only [resCR, torusC_add_two_pi_right, fourierSumC_add_two_pi_right,
    (sin_cos_add_two_pi ψ).1, (sin_cos_add_two_pi ψ).2]

theorem resCZ_add_two_pi_right (D : ℕ) (ι : ℝ) (recs : List TRec) (θ ψ : ℂ) :
    resCZ D ι recs θ (ψ + 2 * Real.pi) = resCZ D ι recs θ ψ := by
  simp only [resCZ, torusC_add_two_pi_right, fourierSumC_add_two_pi_right,
    (sin_cos_add_two_pi ψ).1, (sin_cos_add_two_pi ψ).2]

/-! ## Holomorphy -/

theorem torusC_differentiableOn (D : ℕ) (recs : List TRec) (ρ' : ℝ) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => torusC D recs p.1 p.2) (stripC ρ' ×ˢ stripC ρ') := by
  have hR : InWeighted ρ' (uR D recs) := inWeighted_uOfG _ _ _ _ _
  have hZ : InWeighted ρ' (uZ D recs) := inWeighted_uOfG _ _ _ _ _
  have h : DifferentiableOn ℂ (fun q : (ℂ × ℂ) × (ℂ × ℂ) =>
      torusMapC (uR D recs) (uZ D recs) q.1.1 q.1.2 q.2.1 q.2.2)
      ((stripC ρ' ×ˢ stripC ρ') ×ˢ univ) := differentiableOn_torusMapC hR hZ
  have hin : DifferentiableOn ℂ (fun p : ℂ × ℂ => ((p.1, p.2), ((0 : ℂ), (0 : ℂ))))
      (stripC ρ' ×ˢ stripC ρ') :=
    (differentiableOn_id.prodMk (differentiableOn_const _))
  have hmaps : MapsTo (fun p : ℂ × ℂ => ((p.1, p.2), ((0 : ℂ), (0 : ℂ))))
      (stripC ρ' ×ˢ stripC ρ') ((stripC ρ' ×ˢ stripC ρ') ×ˢ univ) := fun p hp => ⟨hp, trivial⟩
  exact (h.comp hin hmaps).congr fun p _ => rfl

/-- The field components along the complexified torus are holomorphic when the strip is mapped
into the coil neighbourhood. -/
theorem fieldC_differentiableOn {D : ℕ} {recs : List TRec} {ρ' w d η : ℝ} (hw : 0 ≤ w)
    (hη : 0 ≤ η) (hηd : η < d) (hwd : w + d ≤ 7 / 20)
    (hmap : ∀ θ ψ : ℂ, θ ∈ stripC ρ' → ψ ∈ stripC ρ' → torusC D recs θ ψ ∈ coilNbhdP w η)
    (i : Fin 3) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => coilFieldCC (torusC D recs p.1 p.2) i)
      (stripC ρ' ×ˢ stripC ρ') :=
  (coilFieldCC_apply_differentiableOn hw hη hηd hwd i).comp (torusC_differentiableOn D recs ρ')
    fun p hp => hmap p.1 p.2 hp.1 hp.2

theorem resCR_differentiableOn {D : ℕ} {ι : ℝ} {recs : List TRec} {ρ' w d η : ℝ} (hw : 0 ≤ w)
    (hη : 0 ≤ η) (hηd : η < d) (hwd : w + d ≤ 7 / 20)
    (hmap : ∀ θ ψ : ℂ, θ ∈ stripC ρ' → ψ ∈ stripC ρ' → torusC D recs θ ψ ∈ coilNbhdP w η) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => resCR D ι recs p.1 p.2) (stripC ρ' ×ˢ stripC ρ') := by
  have F0 := fieldC_differentiableOn hw hη hηd hwd hmap 0
  have F1 := fieldC_differentiableOn hw hη hηd hwd hmap 1
  have hL := differentiableOn_fourierSumC
    (inWeighted_uOfG (lsym ι) D (fun r => (r.a, r.a')) recs ρ')
  have hR := differentiableOn_fourierSumC
    (inWeighted_uOfG (fun _ => 1) D (fun r => (r.a, r.a')) recs ρ')
  have hs : DifferentiableOn ℂ (fun p : ℂ × ℂ => Complex.sin p.2) (stripC ρ' ×ˢ stripC ρ') := by
    fun_prop
  have hc : DifferentiableOn ℂ (fun p : ℂ × ℂ => Complex.cos p.2) (stripC ρ' ×ˢ stripC ρ') := by
    fun_prop
  exact (((hs.neg.mul F0).add (hc.mul F1)).mul hL).sub (hR.mul ((hc.mul F0).add (hs.mul F1)))

theorem resCZ_differentiableOn {D : ℕ} {ι : ℝ} {recs : List TRec} {ρ' w d η : ℝ} (hw : 0 ≤ w)
    (hη : 0 ≤ η) (hηd : η < d) (hwd : w + d ≤ 7 / 20)
    (hmap : ∀ θ ψ : ℂ, θ ∈ stripC ρ' → ψ ∈ stripC ρ' → torusC D recs θ ψ ∈ coilNbhdP w η) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => resCZ D ι recs p.1 p.2) (stripC ρ' ×ˢ stripC ρ') := by
  have F0 := fieldC_differentiableOn hw hη hηd hwd hmap 0
  have F1 := fieldC_differentiableOn hw hη hηd hwd hmap 1
  have F2 := fieldC_differentiableOn hw hη hηd hwd hmap 2
  have hL := differentiableOn_fourierSumC
    (inWeighted_uOfG (lsym ι) D (fun r => (r.b, r.b')) recs ρ')
  have hR := differentiableOn_fourierSumC
    (inWeighted_uOfG (fun _ => 1) D (fun r => (r.a, r.a')) recs ρ')
  have hs : DifferentiableOn ℂ (fun p : ℂ × ℂ => Complex.sin p.2) (stripC ρ' ×ˢ stripC ρ') := by
    fun_prop
  have hc : DifferentiableOn ℂ (fun p : ℂ × ℂ => Complex.cos p.2) (stripC ρ' ×ˢ stripC ρ') := by
    fun_prop
  exact (((hs.neg.mul F0).add (hc.mul F1)).mul hL).sub (hR.mul F2)

/-! ## Sup bounds on the closed strip -/

theorem norm_sin_le_cosh (z : ℂ) : ‖Complex.sin z‖ ≤ Real.cosh z.im := by
  have h : ‖Complex.sin z‖ ^ 2 ≤ Real.cosh z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, re_sin, im_sin]
    have h1 := Real.sin_sq_add_cos_sq z.re
    have h2 := Real.cosh_sq_sub_sinh_sq z.im
    nlinarith [sq_nonneg (Real.sin z.re), sq_nonneg (Real.sinh z.im), sq_nonneg (Real.cos z.re)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.cosh_pos _).le two_ne_zero).1 h

theorem norm_cos_le_cosh (z : ℂ) : ‖Complex.cos z‖ ≤ Real.cosh z.im := by
  have h : ‖Complex.cos z‖ ^ 2 ≤ Real.cosh z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, re_cos, im_cos]
    have h1 := Real.sin_sq_add_cos_sq z.re
    have h2 := Real.cosh_sq_sub_sinh_sq z.im
    nlinarith [sq_nonneg (Real.sin z.re), sq_nonneg (Real.sinh z.im), sq_nonneg (Real.cos z.re)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.cosh_pos _).le two_ne_zero).1 h

/-- **Sup bound of `E_R` on the closed strip** from bounds `C ≥ cosh(Im ψ)`, the field bound
`Mc` on the neighbourhood and bounds `SL`, `SR` of `|𝓛R|`, `|R|`. -/
theorem norm_resCR_le {D : ℕ} {ι : ℝ} {recs : List TRec} {w d η : ℝ} (hw : 0 ≤ w)
    (hηd : η < d) (hwd : w + d ≤ 7 / 20) {θ ψ : ℂ} (hmem : torusC D recs θ ψ ∈ coilNbhdP w η)
    {C SL SR : ℝ} (hC : Real.cosh ψ.im ≤ C) (hL : ‖fourierSumC (uLR D ι recs) θ ψ‖ ≤ SL)
    (hR : ‖fourierSumC (uR D recs) θ ψ‖ ≤ SR) :
    ‖resCR D ι recs θ ψ‖ ≤ 2 * C * Mcoil w d η * SL + SR * (2 * C * Mcoil w d η) := by
  unfold resCR
  simp only
  have F0 := norm_coilFieldCC_apply_le hw hηd hwd hmem 0
  have F1 := norm_coilFieldCC_apply_le hw hηd hwd hmem 1
  have hs := (norm_sin_le_cosh ψ).trans hC
  have hc := (norm_cos_le_cosh ψ).trans hC
  have hC0 : 0 ≤ C := (Real.cosh_pos _).le.trans hC
  have hM0 : 0 ≤ Mcoil w d η := (norm_nonneg _).trans F0
  have hB : ‖-Complex.sin ψ * coilFieldCC (torusC D recs θ ψ) 0 +
      Complex.cos ψ * coilFieldCC (torusC D recs θ ψ) 1‖ ≤ 2 * C * Mcoil w d η := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_neg]
    nlinarith [norm_nonneg (Complex.sin ψ), norm_nonneg (Complex.cos ψ),
      norm_nonneg (coilFieldCC (torusC D recs θ ψ) 0),
      norm_nonneg (coilFieldCC (torusC D recs θ ψ) 1)]
  have hB' : ‖Complex.cos ψ * coilFieldCC (torusC D recs θ ψ) 0 +
      Complex.sin ψ * coilFieldCC (torusC D recs θ ψ) 1‖ ≤ 2 * C * Mcoil w d η := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    nlinarith [norm_nonneg (Complex.sin ψ), norm_nonneg (Complex.cos ψ),
      norm_nonneg (coilFieldCC (torusC D recs θ ψ) 0),
      norm_nonneg (coilFieldCC (torusC D recs θ ψ) 1)]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have hSL : 0 ≤ SL := (norm_nonneg _).trans hL
  exact add_le_add (mul_le_mul hB hL (norm_nonneg _) (by positivity))
    (mul_le_mul hR hB' (norm_nonneg _) ((norm_nonneg _).trans hR))

/-- **Sup bound of `E_z` on the closed strip.** -/
theorem norm_resCZ_le {D : ℕ} {ι : ℝ} {recs : List TRec} {w d η : ℝ} (hw : 0 ≤ w)
    (hηd : η < d) (hwd : w + d ≤ 7 / 20) {θ ψ : ℂ} (hmem : torusC D recs θ ψ ∈ coilNbhdP w η)
    {C SL SR : ℝ} (hC : Real.cosh ψ.im ≤ C) (hL : ‖fourierSumC (uLZ D ι recs) θ ψ‖ ≤ SL)
    (hR : ‖fourierSumC (uR D recs) θ ψ‖ ≤ SR) :
    ‖resCZ D ι recs θ ψ‖ ≤ 2 * C * Mcoil w d η * SL + SR * Mcoil w d η := by
  unfold resCZ
  simp only
  have F0 := norm_coilFieldCC_apply_le hw hηd hwd hmem 0
  have F1 := norm_coilFieldCC_apply_le hw hηd hwd hmem 1
  have F2 := norm_coilFieldCC_apply_le hw hηd hwd hmem 2
  have hs := (norm_sin_le_cosh ψ).trans hC
  have hc := (norm_cos_le_cosh ψ).trans hC
  have hC0 : 0 ≤ C := (Real.cosh_pos _).le.trans hC
  have hM0 : 0 ≤ Mcoil w d η := (norm_nonneg _).trans F0
  have hB : ‖-Complex.sin ψ * coilFieldCC (torusC D recs θ ψ) 0 +
      Complex.cos ψ * coilFieldCC (torusC D recs θ ψ) 1‖ ≤ 2 * C * Mcoil w d η := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_neg]
    nlinarith [norm_nonneg (Complex.sin ψ), norm_nonneg (Complex.cos ψ),
      norm_nonneg (coilFieldCC (torusC D recs θ ψ) 0),
      norm_nonneg (coilFieldCC (torusC D recs θ ψ) 1)]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have hSL : 0 ≤ SL := (norm_nonneg _).trans hL
  exact add_le_add (mul_le_mul hB hL (norm_nonneg _) (by positivity))
    (mul_le_mul hR F2 (norm_nonneg _) ((norm_nonneg _).trans hR))

/-- Sanity: at real points `‖sin x‖ ≤ cosh 0 = 1`. -/
theorem norm_sin_ofReal_le (x : ℝ) : ‖Complex.sin x‖ ≤ 1 := by
  have := norm_sin_le_cosh (x : ℂ)
  simpa using this

/-! ## The mapping hypothesis -/

/-- The first record carries the mean: `R = a₀/D + R_rest`. -/
theorem Rr_cons_zero (D : ℕ) (r0 : TRec) (h0 : r0.k = 0 ∧ r0.m = 0) (rest : List TRec) (θ ψ : ℝ) :
    Rr D (r0 :: rest) θ ψ = r0.a / D + Rr D rest θ ψ ∧
      Zr D (r0 :: rest) θ ψ = r0.b / D + Zr D rest θ ψ := by
  simp [Rr, Zr, TRec.ang, h0.1, h0.2]

theorem abs_Rr_le (D : ℕ) (recs : List TRec) (θ ψ : ℝ) :
    |Rr D recs θ ψ| ≤ (recs.map fun r => ((r.a.natAbs + r.a'.natAbs : ℕ) : ℝ) / D).sum ∧
    |Zr D recs θ ψ| ≤ (recs.map fun r => ((r.b.natAbs + r.b'.natAbs : ℕ) : ℝ) / D).sum := by
  have key : ∀ (c c' : ℤ) (x : ℝ), |((c : ℝ) * Real.cos x + c' * Real.sin x) / D| ≤
      ((c.natAbs + c'.natAbs : ℕ) : ℝ) / D := by
    intro c c' x
    rw [abs_div, Nat.abs_cast]
    gcongr
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, Nat.cast_add, natAbs_cast, natAbs_cast]
    have := Real.abs_cos_le_one x
    have := Real.abs_sin_le_one x
    nlinarith [abs_nonneg (c : ℝ), abs_nonneg (c' : ℝ)]
  have gen : ∀ (f : TRec → ℝ) (g : TRec → ℝ) (l : List TRec), (∀ r, |f r| ≤ g r) →
      |(l.map f).sum| ≤ (l.map g).sum := by
    intro f g l h
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add_le _ _).trans (add_le_add (h a) ih)
  exact ⟨gen _ _ recs fun r => key _ _ _, gen _ _ recs fun r => key _ _ _⟩

theorem norm_cylR_sub_le (R R' φ Z Z' : ℝ) : ‖cylR R φ Z - cylR R' φ Z'‖ ≤ |R - R'| + |Z - Z'| := by
  have h : ‖cylR R φ Z - cylR R' φ Z'‖ ^ 2 ≤ (|R - R'| + |Z - Z'|) ^ 2 := by
    rw [norm_sq_space']
    simp only [FourierSumHolo.cylR, PiLp.sub_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    have hcs := Real.sin_sq_add_cos_sq φ
    have e : (R * Real.cos φ - R' * Real.cos φ) ^ 2 + (R * Real.sin φ - R' * Real.sin φ) ^ 2 +
        (Z - Z') ^ 2 = (R - R') ^ 2 + (Z - Z') ^ 2 := by
      linear_combination (R - R') ^ 2 * hcs
    rw [e, add_sq, sq_abs, sq_abs]
    nlinarith [abs_nonneg (R - R'), abs_nonneg (Z - Z')]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

/-- **The mapping hypothesis from numerical bounds**: if the real torus satisfies
`|R - 1| ≤ s₁`, `|z| ≤ s₂`, the complexification moves `R`, `z` by at most `e_R`, `e_z` on the
strip `ρ'`, and `C ≥ cosh ρ'`, `Sh ≥ sinh ρ'`, then the complexified torus maps the open strip into
`coilNbhdP w η` as soon as `(e_R C)² + ((1+s₁+e_R) Sh)² + e_z² < η²` and
`max s₁ s₂ + (1+s₁+e_R)(C-1) + e_R Sh + e_R + e_z < w`. -/
theorem torus_hmap {D : ℕ} {recs : List TRec} {ρ' s₁ s₂ eR eZ C Sh w η : ℝ}
    (hs₁ : ∀ θ ψ : ℝ, |Rr D recs θ ψ - 1| ≤ s₁) (hs₂ : ∀ θ ψ : ℝ, |Zr D recs θ ψ| ≤ s₂)
    (hs₁1 : s₁ < 1)
    (heR : ∀ θ ψ : ℂ, |θ.im| ≤ ρ' → |ψ.im| ≤ ρ' →
      ‖fourierSumC (uR D recs) θ ψ - fourierSumC (uR D recs) θ.re ψ.re‖ ≤ eR)
    (heZ : ∀ θ ψ : ℂ, |θ.im| ≤ ρ' → |ψ.im| ≤ ρ' →
      ‖fourierSumC (uZ D recs) θ ψ - fourierSumC (uZ D recs) θ.re ψ.re‖ ≤ eZ)
    (hρ' : 0 ≤ ρ') (hC : Real.cosh ρ' ≤ C) (hSh : Real.sinh ρ' ≤ Sh) (hη : 0 < η)
    (him : (eR * C) ^ 2 + ((1 + s₁ + eR) * Sh) ^ 2 + eZ ^ 2 < η ^ 2)
    (hre : max s₁ s₂ + ((1 + s₁ + eR) * (C - 1) + eR * Sh) + eR + eZ < w) :
    ∀ θ ψ : ℂ, θ ∈ stripC ρ' → ψ ∈ stripC ρ' → torusC D recs θ ψ ∈ coilNbhdP w η := by
  intro θ ψ hθ hψ
  have hθ' : |θ.im| ≤ ρ' := (show |θ.im| < ρ' from hθ).le
  have hψ' : |ψ.im| ≤ ρ' := (show |ψ.im| < ρ' from hψ).le
  set R := fourierSumC (uR D recs) θ ψ
  set Z := fourierSumC (uZ D recs) θ ψ
  set R₀ := Rr D recs θ.re ψ.re
  set Z₀ := Zr D recs θ.re ψ.re
  have dR : ‖R - (R₀ : ℂ)‖ ≤ eR := by
    have := heR θ ψ hθ' hψ'; rwa [fourierSumC_uR_ofReal] at this
  have dZ : ‖Z - (Z₀ : ℂ)‖ ≤ eZ := by
    have := heZ θ ψ hθ' hψ'; rwa [fourierSumC_uZ_ofReal] at this
  have eR0 : 0 ≤ eR := (norm_nonneg _).trans dR
  have eZ0 : 0 ≤ eZ := (norm_nonneg _).trans dZ
  have hRim : |R.im| ≤ eR := by
    have := (Complex.abs_im_le_norm (R - (R₀ : ℂ))).trans dR; simpa using this
  have hZim : |Z.im| ≤ eZ := by
    have := (Complex.abs_im_le_norm (Z - (Z₀ : ℂ))).trans dZ; simpa using this
  have hRre : |R.re - R₀| ≤ eR := by
    have := (Complex.abs_re_le_norm (R - (R₀ : ℂ))).trans dR; simpa using this
  have hZre : |Z.re - Z₀| ≤ eZ := by
    have := (Complex.abs_re_le_norm (Z - (Z₀ : ℂ))).trans dZ; simpa using this
  have hR₀ := hs₁ θ.re ψ.re
  have hZ₀ := hs₂ θ.re ψ.re
  have hRabs : |R.re| ≤ 1 + s₁ + eR := by
    have h1 : |R.re| ≤ |R.re - R₀| + |R₀| := by
      have := abs_add_le (R.re - R₀) R₀; rwa [sub_add_cancel] at this
    have h2 : |R₀| ≤ 1 + s₁ := by
      have := abs_add_le (R₀ - 1) 1; rw [sub_add_cancel] at this; simp at this; linarith
    linarith
  -- hyperbolic bounds
  have hcosh : Real.cosh ψ.im ≤ C :=
    (Real.cosh_le_cosh.2 (by rw [abs_of_nonneg hρ']; exact hψ')).trans hC
  have hcosh1 : 1 ≤ Real.cosh ψ.im := Real.one_le_cosh _
  have hsinh : |Real.sinh ψ.im| ≤ Sh := by
    rw [Real.abs_sinh]; exact (Real.sinh_le_sinh.2 hψ').trans hSh
  have hSh0 : 0 ≤ Sh := (abs_nonneg _).trans hsinh
  have hT : torusC D recs θ ψ = cylC R ψ Z := by simp [torusC, torusMapC, R, Z]
  rw [hT]
  -- imaginary part
  have hIm : ‖imV (cylC R ψ Z)‖ < η := by
    have hsq := norm_imV_cylC_sq R ψ Z
    have b1 : R.im ^ 2 * Real.cosh ψ.im ^ 2 ≤ (eR * C) ^ 2 := by
      rw [← mul_pow, ← sq_abs (R.im * Real.cosh ψ.im)]
      exact pow_le_pow_left₀ (abs_nonneg _) (by
        rw [abs_mul, abs_of_pos (Real.cosh_pos _)]
        exact mul_le_mul hRim hcosh (Real.cosh_pos _).le eR0) 2
    have b2 : R.re ^ 2 * Real.sinh ψ.im ^ 2 ≤ ((1 + s₁ + eR) * Sh) ^ 2 := by
      rw [← mul_pow, ← sq_abs (R.re * Real.sinh ψ.im)]
      exact pow_le_pow_left₀ (abs_nonneg _)
        (by
          rw [abs_mul]
          exact mul_le_mul hRabs hsinh (abs_nonneg _) (by linarith [abs_nonneg R.re])) 2
    have b3 : Z.im ^ 2 ≤ eZ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hZim 2
    have : ‖imV (cylC R ψ Z)‖ ^ 2 < η ^ 2 := by rw [hsq]; linarith
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hη.le two_ne_zero).1 this
  -- real part
  have hReD : ‖reV (cylC R ψ Z) - cylR R.re ψ.re Z.re‖ ≤
      (1 + s₁ + eR) * (C - 1) + eR * Sh := by
    have hsq := norm_reV_cylC_sub_sq R ψ Z
    have b1 : R.re ^ 2 * (Real.cosh ψ.im - 1) ^ 2 ≤ ((1 + s₁ + eR) * (C - 1)) ^ 2 := by
      rw [← mul_pow, ← sq_abs (R.re * (Real.cosh ψ.im - 1))]
      exact pow_le_pow_left₀ (abs_nonneg _) (by
        rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ Real.cosh ψ.im - 1)]
        exact mul_le_mul hRabs (by linarith) (by linarith) (by linarith [abs_nonneg R.re])) 2
    have b2 : R.im ^ 2 * Real.sinh ψ.im ^ 2 ≤ (eR * Sh) ^ 2 := by
      rw [← mul_pow, ← sq_abs (R.im * Real.sinh ψ.im)]
      exact pow_le_pow_left₀ (abs_nonneg _)
        (by rw [abs_mul]; exact mul_le_mul hRim hsinh (abs_nonneg _) eR0) 2
    have hC1 : 0 ≤ (1 + s₁ + eR) * (C - 1) := by
      have : 0 ≤ 1 + s₁ + eR := by linarith [abs_nonneg R.re]
      exact mul_nonneg this (by linarith)
    have : ‖reV (cylC R ψ Z) - cylR R.re ψ.re Z.re‖ ^ 2 ≤
        ((1 + s₁ + eR) * (C - 1) + eR * Sh) ^ 2 := by
      rw [hsq]; nlinarith [mul_nonneg hC1 (mul_nonneg eR0 hSh0)]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 this
  have hpt : torusPt D recs θ.re ψ.re ∈ realTube (max s₁ s₂) := by
    refine ⟨?_, ?_⟩
    · simp only [torusPt, FourierSumHolo.cylR]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      have hpos : 0 < R₀ := by
        have := (abs_le.1 hR₀).1; linarith
      have e : Real.sqrt ((R₀ * Real.cos ψ.re) ^ 2 + (R₀ * Real.sin ψ.re) ^ 2) = R₀ := by
        rw [show (R₀ * Real.cos ψ.re) ^ 2 + (R₀ * Real.sin ψ.re) ^ 2 = R₀ ^ 2 by
          linear_combination R₀ ^ 2 * Real.cos_sq_add_sin_sq ψ.re, Real.sqrt_sq hpos.le]
      rw [e]; exact hR₀.trans (le_max_left _ _)
    · simp only [torusPt, FourierSumHolo.cylR]
      simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      exact hZ₀.trans (le_max_right _ _)
  have hdist : ‖reV (cylC R ψ Z) - torusPt D recs θ.re ψ.re‖ ≤
      ((1 + s₁ + eR) * (C - 1) + eR * Sh) + eR + eZ := by
    have h2 := norm_cylR_sub_le R.re R₀ ψ.re Z.re Z₀
    calc ‖reV (cylC R ψ Z) - torusPt D recs θ.re ψ.re‖
        ≤ ‖reV (cylC R ψ Z) - cylR R.re ψ.re Z.re‖ +
          ‖cylR R.re ψ.re Z.re - torusPt D recs θ.re ψ.re‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by
          have : torusPt D recs θ.re ψ.re = cylR R₀ ψ.re Z₀ := rfl
          rw [this]; linarith
  have hT2 := realTube_of_dist hpt hdist
  refine ⟨?_, ?_, hIm⟩
  · have := hT2.1
    simp only [reV_apply] at this
    linarith
  · have := hT2.2
    simp only [reV_apply] at this
    linarith

end PlasmaLean.Design.CoilKam
