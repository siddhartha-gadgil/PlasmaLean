/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamAFinal
public import PlasmaLean.Design.DommaschkKamCFinal

/-!
# A nested certified region of the Dommaschk field: tori C (inner) and A (outer)

On-demand top module (not imported by `PlasmaLean.lean`). Build:
`lake build PlasmaLean.Design.DommaschkKamNested` after `DommaschkKamCFinal` and
`DommaschkKamAFinal` (build stale dependencies one at a time).

**Nesting, the definition (`NestedTori`).** Two cylindrical tori `(R_C, z_C)`, `(R_A, z_A)`
(functions of `(θ, φ)`) are *nested about a reference curve* `(R₀(φ), z₀(φ))` with poloidal
angles `Θ_C`, `Θ_A` if
* both satisfy the poloidal-angle convention of the contract about this **common** curve
  (`PoloidalAngle`: continuous polar angles of `(R − R₀, z − z₀)`, one turn in `θ`, none in `φ`);
* **ray order**: in every cross-section `φ`, along every ray from the reference point, every point
  of C is strictly closer than every point of A: `Θ_C(θ, φ) ≡ Θ_A(θ', φ) (mod 2π)` implies
  `|K_C(θ, φ) − ref(φ)| < |K_A(θ', φ) − ref(φ)|`.

Consequences (`NestedTori.disjoint`, `NestedTori.inside`): the cross-sections are disjoint, and
every point of C lies in the open star-shaped region of A about the reference point,
`ref + s (K_A(θ', φ) − ref)` with `0 ≤ s < 1` (A meets every ray, by the winding of `Θ_A`).

**The certificate** (`Design/DommaschkKamANest`, `…AContract`). The reference curve is the
`θ`-average of the low-resolution surrogate of torus C (`Rref`, `Zref`, explicit). Both exact
tori satisfy the radial condition about it (squared approximate inverses, `radC_pos`, `radA_pos`).
The quadratic gauge `G(ψₒ; X, Y) = a X² + 2 b X Y + d Y²` (`gaugeR`, dyadic trigonometric
coefficients of degree `4` in `ψₒ = 2φ`, the same function for both tori) satisfies
`G < 1` on the exact torus C (`gaugeC_lt`) and `G > 1` on the exact torus A (`gaugeA_gt`):
surrogate margins `0.055` and `0.064` (pointwise minima of `1 − G`, `G − 1`), certified through
`‖q² F − 1‖ ≤ 0.0025`, resp. `0.080`. Homogeneity `G(r e) = r² G(e)` (`gaugeR_smul`) gives the
ray order without any positivity of the form.

**Results.**
* `nested_of_exact`: the exact tori C and A (`ExactTorusC`, `ExactTorusA`) are `NestedTori` about
  `(Rref, Zref)` with `Θref`;
* **`dommaschk_nested`**: the exact Dommaschk field has two certified invariant tori
  (`FieldTorus`, transforms `ι_C = −(85 + √5)/361`, `ι_A = −(19 + √5)/89`), nested;
* **`dommaschk_nested_C1`**: clause C1 on the two-surface family `{C, A}` with `I_max = 0` and
  `ι_min = 0.2386` (`|ι_A| = 0.23861 < 0.24`: `6/25` is not admissible for the family,
  `not_nested_C1_quarter`), together with the nesting of the two surfaces.

**Sanity.** `nestedTori_circles` (two concentric circles of radii `1 < 2` are nested: accepted
fixture), `not_nestedTori_swap` (the same circles in the wrong order are not: rejected fixture).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkKamNested

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Contract WEll1Z2
open PlasmaLean.Design.DommaschkKamA (Rref Zref Θref gaugeR gaugeR_smul rU rZ rad_contract
  eval_psi_rot isReal_rotψi' ExactTorusA surfaceA)
open PlasmaLean.Design.DommaschkKamC (RofC ExactTorusC surfaceC rotψi)
open Real

/-! ## Nested tori -/

/-- The squared distance of a torus point from the reference point. -/
def dist2 (R z : ℝ → ℝ → ℝ) (R₀ z₀ : ℝ → ℝ) (θ φ : ℝ) : ℝ :=
  (R θ φ - R₀ φ) ^ 2 + (z θ φ - z₀ φ) ^ 2

/-- **Two tori nested about a common reference curve**: both have poloidal angles about it, and
along every ray from the reference point every point of the inner torus precedes every point of
the outer one. -/
structure NestedTori (RC zC RA zA : ℝ → ℝ → ℝ) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ) : Prop where
  /-- The inner torus has a poloidal angle about the reference curve. -/
  polarC : PoloidalAngle RC zC R₀ z₀ ΘC
  /-- The outer torus has a poloidal angle about the same reference curve. -/
  polarA : PoloidalAngle RA zA R₀ z₀ ΘA
  /-- Ray order. -/
  ray_lt : ∀ φ θ θ' (k : ℤ), ΘC θ φ = ΘA θ' φ + 2 * π * k →
    dist2 RC zC R₀ z₀ θ φ < dist2 RA zA R₀ z₀ θ' φ

/-- Two unit vectors with the same polar angle mod `2π`. -/
theorem angle_eq_of_cos_sin {a b : ℝ} (hc : cos a = cos b) (hs : sin a = sin b) :
    ∃ k : ℤ, a = b + 2 * π * k := by
  have h : Complex.exp (a * Complex.I) = Complex.exp (b * Complex.I) := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hs]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simp at this
  linarith

/-- The polar radius from the convention. -/
theorem polar_dist2 {R z : ℝ → ℝ → ℝ} {R₀ z₀ : ℝ → ℝ} {Θ : ℝ → ℝ → ℝ}
    (hP : PoloidalAngle R z R₀ z₀ Θ) (θ φ : ℝ) :
    ∃ r, 0 < r ∧ R θ φ - R₀ φ = r * cos (Θ θ φ) ∧ z θ φ - z₀ φ = r * sin (Θ θ φ) ∧
      dist2 R z R₀ z₀ θ φ = r ^ 2 := by
  obtain ⟨r, hr, h1, h2⟩ := hP.polar θ φ
  refine ⟨r, hr, h1, h2, ?_⟩
  rw [dist2, h1, h2]
  linear_combination r ^ 2 * sin_sq_add_cos_sq (Θ θ φ)

namespace NestedTori

variable {RC zC RA zA : ℝ → ℝ → ℝ} {R₀ z₀ : ℝ → ℝ} {ΘC ΘA : ℝ → ℝ → ℝ}

/-- **The cross-sections are disjoint.** -/
theorem disjoint (h : NestedTori RC zC RA zA R₀ z₀ ΘC ΘA) (θ θ' φ : ℝ) :
    (RC θ φ, zC θ φ) ≠ (RA θ' φ, zA θ' φ) := by
  intro he
  obtain ⟨h1, h2⟩ := Prod.mk.inj he
  obtain ⟨r, hr, a1, a2, d1⟩ := polar_dist2 h.polarC θ φ
  obtain ⟨s, hs, b1, b2, d2⟩ := polar_dist2 h.polarA θ' φ
  have hd : dist2 RC zC R₀ z₀ θ φ = dist2 RA zA R₀ z₀ θ' φ := by simp only [dist2, h1, h2]
  have hrs : r = s := by
    have : r ^ 2 = s ^ 2 := by rw [← d1, ← d2, hd]
    nlinarith
  subst hrs
  have hc : cos (ΘC θ φ) = cos (ΘA θ' φ) := by
    apply mul_left_cancel₀ hr.ne'; rw [← a1, ← b1, h1]
  have hs' : sin (ΘC θ φ) = sin (ΘA θ' φ) := by
    apply mul_left_cancel₀ hr.ne'; rw [← a2, ← b2, h2]
  obtain ⟨k, hk⟩ := angle_eq_of_cos_sin hc hs'
  have := h.ray_lt φ θ θ' k hk
  rw [hd] at this
  exact lt_irrefl _ this

/-- The outer torus meets every ray: every angle is a value of `Θ_A(·, φ)` mod `2π`. -/
theorem exists_angle (h : NestedTori RC zC RA zA R₀ z₀ ΘC ΘA) (α φ : ℝ) :
    ∃ θ', ΘA θ' φ = α := by
  have hc : Continuous fun t => ΘA t φ :=
    h.polarA.continuous.comp (continuous_id.prodMk continuous_const)
  have hw : ∀ (n : ℕ) (t : ℝ), ΘA (t + 2 * π * n) φ = ΘA t φ + 2 * π * n := by
    intro n
    induction n with
    | zero => intro t; simp
    | succ n ih =>
      intro t
      rw [show t + 2 * π * ((n + 1 : ℕ) : ℝ) = (t + 2 * π * n) + 2 * π by push_cast; ring,
        h.polarA.wind_θ, ih]
      push_cast; ring
  have hw' : ∀ (n : ℕ) (t : ℝ), ΘA (t - 2 * π * n) φ = ΘA t φ - 2 * π * n := by
    intro n t
    have := hw n (t - 2 * π * n)
    rw [sub_add_cancel] at this
    linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((|α| + |ΘA 0 φ|) / (2 * π))
  have hpi : 0 < 2 * π := by positivity
  have hn' : |α| + |ΘA 0 φ| < 2 * π * n := by
    rw [div_lt_iff₀ hpi] at hn; linarith
  have hlo : ΘA (0 - 2 * π * n) φ ≤ α := by
    rw [hw']; have := neg_abs_le α; have := le_abs_self (ΘA 0 φ); linarith
  have hhi : α ≤ ΘA (0 + 2 * π * n) φ := by
    rw [hw]; have := le_abs_self α; have := neg_abs_le (ΘA 0 φ); linarith
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc (by nlinarith [Real.pi_pos] :
    (0 : ℝ) - 2 * π * n ≤ 0 + 2 * π * n) hc.continuousOn ⟨hlo, hhi⟩
  exact ⟨t, ht⟩

/-- **The inner torus lies inside the outer one**: every point of C is
`ref + s (K_A(θ', φ) − ref)` for some `θ'` and `0 ≤ s < 1`. -/
theorem inside (h : NestedTori RC zC RA zA R₀ z₀ ΘC ΘA) (θ φ : ℝ) :
    ∃ θ' s, 0 ≤ s ∧ s < 1 ∧ RC θ φ = R₀ φ + s * (RA θ' φ - R₀ φ) ∧
      zC θ φ = z₀ φ + s * (zA θ' φ - z₀ φ) := by
  obtain ⟨θ', hθ'⟩ := h.exists_angle (ΘC θ φ) φ
  obtain ⟨r, hr, a1, a2, d1⟩ := polar_dist2 h.polarC θ φ
  obtain ⟨s, hs, b1, b2, d2⟩ := polar_dist2 h.polarA θ' φ
  have hlt := h.ray_lt φ θ θ' 0 (by rw [hθ']; simp)
  rw [d1, d2] at hlt
  have hrs : r < s := by nlinarith
  refine ⟨θ', r / s, by positivity, (div_lt_one hs).2 hrs, ?_, ?_⟩
  · rw [b1, hθ', show r / s * (s * cos (ΘC θ φ)) = r * cos (ΘC θ φ) by field_simp]
    linarith [a1]
  · rw [b2, hθ', show r / s * (s * sin (ΘC θ φ)) = r * sin (ΘC θ φ) by field_simp]
    linarith [a2]

end NestedTori

/-! ## Fixtures -/

/-- The circle of radius `ρ` about `(R₀, 0)` with angle `θ`. -/
def circR (ρ : ℝ) (θ _φ : ℝ) : ℝ := 2 + ρ * cos θ

/-- Its height. -/
def circZ (ρ : ℝ) (θ _φ : ℝ) : ℝ := ρ * sin θ

/-- The identity angle. -/
def idΘ (θ _φ : ℝ) : ℝ := θ

/-- The circle of radius `ρ > 0` has the identity poloidal angle about `(2, 0)`. -/
theorem circ_polar {ρ : ℝ} (hρ : 0 < ρ) :
    PoloidalAngle (circR ρ) (circZ ρ) (fun _ => 2) (fun _ => 0) idΘ where
  continuous_R₀ := continuous_const
  continuous_z₀ := continuous_const
  per_R₀ _ := rfl
  per_z₀ _ := rfl
  continuous := continuous_fst
  polar θ φ := ⟨ρ, hρ, by simp [circR, idΘ], by simp [circZ, idΘ]⟩
  wind_θ _ _ := rfl
  wind_φ _ _ := rfl

/-- The squared distance on a circle. -/
theorem dist2_circ (ρ θ φ : ℝ) :
    dist2 (circR ρ) (circZ ρ) (fun _ => 2) (fun _ => 0) θ φ = ρ ^ 2 := by
  simp only [dist2, circR, circZ]
  linear_combination ρ ^ 2 * sin_sq_add_cos_sq θ

/-- **Accepted fixture**: concentric circles of radii `1 < 2` are nested. -/
theorem nestedTori_circles :
    NestedTori (circR 1) (circZ 1) (circR 2) (circZ 2) (fun _ => 2) (fun _ => 0) idΘ idΘ where
  polarC := circ_polar one_pos
  polarA := circ_polar two_pos
  ray_lt φ θ θ' _ _ := by rw [dist2_circ, dist2_circ]; norm_num

/-- **Rejected fixture**: in the wrong order the circles are not nested. -/
theorem not_nestedTori_swap :
    ¬ NestedTori (circR 2) (circZ 2) (circR 1) (circZ 1) (fun _ => 2) (fun _ => 0) idΘ idΘ :=
  fun h => by
    have := h.ray_lt 0 0 0 0 (by simp [idΘ])
    rw [dist2_circ, dist2_circ] at this
    norm_num at this

/-! ## The exact tori are nested -/

/-- The common reference point in oracle coordinates. -/
theorem dist_coords (u : FA) (θ φ : ℝ) :
    RofC u θ φ - Rref φ = (eval (rotψi u) θ (2 * φ)).re - (eval rU 0 (2 * φ)).re := by
  simp only [RofC, Rref, Zof, eval_psi_rot]; ring

/-- The common reference height in oracle coordinates. -/
theorem dist_coordsZ (z : FA) (θ φ : ℝ) :
    Zof z θ φ - Zref φ = (eval (rotψi z) θ (2 * φ)).re - (eval rZ 0 (2 * φ)).re := by
  simp only [Zof, Zref, eval_psi_rot]

/-- **The exact tori C and A are nested** about the common reference curve. -/
theorem nested_of_exact {uC zC uA zA : FA} (hC : ExactTorusC uC zC) (hA : ExactTorusA uA zA) :
    NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) Rref Zref (Θref uC zC) (Θref uA zA) where
  polarC := DommaschkKamA.ExactTorusC'.poloidalAngle hC
  polarA := hA.poloidalAngle
  ray_lt φ θ θ' k hk := by
    obtain ⟨r, hr, a1, a2, d1⟩ := polar_dist2 (DommaschkKamA.ExactTorusC'.poloidalAngle hC) θ φ
    obtain ⟨s, hs, b1, b2, d2⟩ := polar_dist2 hA.poloidalAngle θ' φ
    have gC := DommaschkKamA.gaugeC_lt (isReal_rotψi' hC.real_u) (isReal_rotψi' hC.real_z)
      (DommaschkKamA.ExactTorusC'.osc_U hC) (DommaschkKamA.ExactTorusC'.osc_Z hC) θ (2 * φ)
    have gA := DommaschkKamA.gaugeA_gt (isReal_rotψi' hA.real_u) (isReal_rotψi' hA.real_z)
      hA.osc_U hA.osc_Z θ' (2 * φ)
    rw [← dist_coords, ← dist_coordsZ, a1, a2, hk] at gC
    rw [← dist_coords, ← dist_coordsZ, b1, b2] at gA
    have ec : cos (Θref uA zA θ' φ + 2 * π * k) = cos (Θref uA zA θ' φ) := by
      rw [show (2 : ℝ) * π * k = (k : ℝ) * (2 * π) by ring]; exact cos_add_int_mul_two_pi _ _
    have es : sin (Θref uA zA θ' φ + 2 * π * k) = sin (Θref uA zA θ' φ) := by
      rw [show (2 : ℝ) * π * k = (k : ℝ) * (2 * π) by ring]; exact sin_add_int_mul_two_pi _ _
    rw [ec, es, gaugeR_smul] at gC
    rw [gaugeR_smul] at gA
    rw [d1, d2]
    set g := gaugeR (2 * φ) (cos (Θref uA zA θ' φ)) (sin (Θref uA zA θ' φ))
    have hg : 0 < g := by
      by_contra hg
      have hg' := not_lt.mp hg
      nlinarith [sq_nonneg s]
    have h1 : r ^ 2 * g < s ^ 2 * g := by linarith
    exact lt_of_mul_lt_mul_right h1 hg.le

/-! ## The nested certified region -/

/-- **A nested certified region of the exact Dommaschk field**: two certified invariant tori,
with transforms `ι_C = −(85 + √5)/361` (inner) and `ι_A = −(19 + √5)/89` (outer), nested about
a common reference curve. -/
theorem dommaschk_nested :
    ∃ (RC zC RA zA : ℝ → ℝ → ℝ) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      FieldTorus (DommaschkQA2R.field DommaschkQA2R.candidate) RC zC DommaschkKamDio.dkIotaC ∧
      FieldTorus (DommaschkQA2R.field DommaschkQA2R.candidate) RA zA DommaschkKamDio.dkIotaA ∧
      NestedTori RC zC RA zA R₀ z₀ ΘC ΘA := by
  obtain ⟨uC, zC, huC, hzC, hurC, hzrC, hRC, hZC, hCC⟩ :=
    DommaschkKamC.dk_exact_of_res
      (DommaschkKamC.Bd_weaken DommaschkKamC.dk_e0R DommaschkKamC.e0q_le_budget)
      (DommaschkKamC.Bd_weaken DommaschkKamC.dk_e0Z DommaschkKamC.e0q_le_budget)
  obtain ⟨uA, zA, hA⟩ := DommaschkKamA.exists_exactTorusA
  have hC : ExactTorusC uC zC := ⟨huC, hzC, hurC, hzrC, hRC, hZC, hCC⟩
  exact ⟨_, _, _, _, _, _, _, _, hC.fieldTorus, hA.fieldTorus, nested_of_exact hC hA⟩

/-- **Clause C1 on the nested family `{C, A}`**: for every `μ₀ > 0` there are two surfaces, with
transforms `ι_C` and `ι_A`, carrying zero net current and `|ι| ≥ 0.2386`, nested about a common
reference curve. -/
theorem dommaschk_nested_C1 {μ₀ : ℝ} (hμ : 0 < μ₀) :
    ∃ (sC sA : SurfaceData) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      sC.iota = DommaschkKamDio.dkIotaC ∧ sA.iota = DommaschkKamDio.dkIotaA ∧
      CurrentFreeTransform μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) {sC, sA} 0
        (1193 / 5000) ∧
      NestedTori sC.R sC.z sA.R sA.z R₀ z₀ ΘC ΘA := by
  obtain ⟨uC, zC, huC, hzC, hurC, hzrC, hRC, hZC, hCC⟩ :=
    DommaschkKamC.dk_exact_of_res
      (DommaschkKamC.Bd_weaken DommaschkKamC.dk_e0R DommaschkKamC.e0q_le_budget)
      (DommaschkKamC.Bd_weaken DommaschkKamC.dk_e0Z DommaschkKamC.e0q_le_budget)
  obtain ⟨uA, zA, hA⟩ := DommaschkKamA.exists_exactTorusA
  have hC : ExactTorusC uC zC := ⟨huC, hzC, hurC, hzrC, hRC, hZC, hCC⟩
  have hιC : (1193 / 5000 : ℝ) ≤ |DommaschkKamDio.dkIotaC| :=
    le_trans (by norm_num) DommaschkKamC.iotaC_ge
  refine ⟨surfaceC uC zC, surfaceA uA zA, _, _, _, _, rfl, rfl, ?_, nested_of_exact hC hA⟩
  refine DommaschkQA2R.candidate_currentFreeTransform hμ (Set.insert_nonempty _ _) (by norm_num)
    ?_ ?_ ?_ ?_
  · rintro s (rfl | rfl)
    · exact DommaschkKamA.ExactTorusC'.iotaOnTorusRef hC
    · exact hA.iotaOnTorus
  · rintro s (rfl | rfl)
    · exact ((DommaschkKamC.contDiff_RofC hC.ana_u).comp
        (contDiff_id.prodMk contDiff_const)).of_le (by norm_num)
    · exact ((DommaschkKamC.contDiff_RofC hA.ana_u).comp
        (contDiff_id.prodMk contDiff_const)).of_le (by norm_num)
  · rintro s (rfl | rfl)
    · exact ((contDiff_Zof hC.ana_z).comp (contDiff_id.prodMk contDiff_const)).of_le
        (by norm_num)
    · exact ((contDiff_Zof hA.ana_z).comp (contDiff_id.prodMk contDiff_const)).of_le
        (by norm_num)
  · rintro s (rfl | rfl)
    · exact hιC
    · exact DommaschkKamA.iotaA_ge

/-- **Rejected fixture**: no family containing torus A certifies `ι_min = 6/25`. -/
theorem not_nested_C1_quarter {μ₀ : ℝ} {sC : SurfaceData} {uA zA : FA} :
    ¬ CurrentFreeTransform μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate)
      {sC, surfaceA uA zA} 0 (6 / 25) := fun h => by
  have := h.iota_ge (surfaceA uA zA) (Set.mem_insert_of_mem _ rfl)
  exact absurd this (not_le.mpr DommaschkKamA.iotaA_lt)

end PlasmaLean.Design.DommaschkKamNested
