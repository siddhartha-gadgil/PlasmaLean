/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCMuInstance
public import PlasmaLean.Design.RationalStellaratorGCCyl

/-!
# The `μ > 0` passing flow form at real points

At a real point `(u, z, cos 2φ, sin 2φ)` with `|u| ≤ 1/4` where the three nodes are valid, the
expression trees of `gcFlowMu ρ λ` (`Design/RationalStellaratorGCMuInstance`) evaluate to real
numbers:

* `eval_eV4_ptC`: `(1 + E₄)^{−1/2} = 1/(R⁴ P₄)`; `eval_eBm_ptC`: the tree `eBm` is
  `|B| = √q/R⁴` (`Bmr`), and `norm_field_cylPt`: this is `‖field (1/4) (cylPt R φ z)‖`;
* `eval_eN_ptC`: `(1 − λ|B|)^{−1/2}`; `eval_eF_ptC`: `F = (1 − λ|B|/2)/√(1 − λ|B|)` (`Fr`);
* `eval_gcDM_ptC`, `eval_gcNRM_ptC`, `eval_gcNZM_ptC`: `D̃, ñ_R, ñ_z` are the real
  guiding-centre flow form `gcDr, gcNRr, gcNZr` of `Design/RationalStellaratorGCCyl` with the
  position-dependent gyro-length `ρ F`.

**Sanity.** `Fr_zero`: `F = 1` for `λ = 0`; `P4u_pos`: `P₄ > 0` for `|u| ≤ 1/4`.
-/

open scoped RealInnerProductSpace

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open Real PlasmaLean.Fields PlasmaLean.Design.RationalStellarator PlasmaLean.Design.KamTorusA
  PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton WEll1Z2 WithLp

/-- The Taylor polynomial `P₄(u) = ∑_{n ≤ 6} (−1)ⁿ C(n+3, 3) uⁿ` of `(1 + u)^{−4}`. -/
def P4u (u : ℝ) : ℝ :=
  1 - 4 * u + 10 * u ^ 2 - 20 * u ^ 3 + 35 * u ^ 4 - 56 * u ^ 5 + 84 * u ^ 6

/-- `P4P` at a real point. -/
theorem eval_P4P_ptC (u z c s wR wZ : ℝ) :
    PolyExpr.eval (ptC u z c s wR wZ) P4P = (P4u u : ℂ) := by
  simp only [PolyExpr.eval, P4P, sumE, monoE, ptC, Matrix.cons_val, Algebra.algebraMap_self,
    RingHom.id_apply, PolyExpr.eval_npow, P4u]
  push_cast; ring

/-- **Sanity**: `P₄(u) > 0` for `|u| ≤ 1/4`. -/
theorem P4u_pos {u : ℝ} (hu : |u| ≤ 1 / 4) : 0 < P4u u := by
  obtain ⟨h1, h2⟩ := abs_le.mp hu
  unfold P4u
  nlinarith [sq_nonneg u, sq_nonneg (u ^ 2), sq_nonneg (u ^ 3), mul_nonneg (sq_nonneg u)
    (sq_nonneg (u - 1 / 4)), pow_two_nonneg (u ^ 2 - u), pow_two_nonneg (u ^ 3 - u ^ 2)]

/-- **`E₄ = R⁸ P₄² − 1`** at a complex point. -/
theorem E4_val_C (x : Fin 6 → ℂ) :
    PolyExpr.eval x E4P = (1 + x 0) ^ 8 * PolyExpr.eval x P4P ^ 2 - 1 := by
  have h := congrArg (PolyExprS.evalAlg 0 0) (E4_val (fun i => algebraMap ℂ FA (x i)))
  have hx : (fun i => PolyExprS.evalAlg 0 0 (algebraMap ℂ FA (x i))) = x := by
    funext i; simp
  simp only [polyExpr_eval_algHom, map_sub, map_mul, map_add, map_pow, map_one, hx] at h
  simpa [PlasmaLean.Theory.KAM.eval_algebraMap] using h

/-- **`Q P P₄ = q P P₄`** at a complex point. -/
theorem QPP4_val_C (x : Fin 6 → ℂ) :
    PolyExpr.eval x QPP4P = (PolyExpr.eval x KamNewton.nRp ^ 2 + (1 + x 0) ^ 2 * PolyExpr.eval x
      KamNewton.Dp ^ 2 + PolyExpr.eval x KamNewton.nZp ^ 2) * PolyExpr.eval x PuP *
      PolyExpr.eval x P4P := by
  have h := congrArg (PolyExprS.evalAlg 0 0) (QPP4_val (fun i => algebraMap ℂ FA (x i)))
  have hx : (fun i => PolyExprS.evalAlg 0 0 (algebraMap ℂ FA (x i))) = x := by
    funext i; simp
  simp only [polyExpr_eval_algHom, map_mul, map_add, map_pow, map_one, hx] at h
  simpa [PlasmaLean.Theory.KAM.eval_algebraMap] using h

/-- `E₄` at a real point. -/
theorem eval_E4P_ptC (u z c s wR wZ : ℝ) :
    PolyExpr.eval (ptC u z c s wR wZ) E4P = (((1 + u) ^ 8 * P4u u ^ 2 - 1 : ℝ) : ℂ) := by
  rw [E4_val_C, eval_P4P_ptC]
  simp only [ptC, Matrix.cons_val_zero]
  push_cast; ring

/-- `Q P P₄` at a real point. -/
theorem eval_QPP4P_ptC (u z c s wR wZ : ℝ) :
    PolyExpr.eval (ptC u z c s wR wZ) QPP4P = ((qr (1 + u) z c s * Pu u * P4u u : ℝ) : ℂ) := by
  rw [QPP4_val_C, eval_nRp_ptC, eval_Dp_ptC, eval_nZp_ptC, eval_PuP_ptC, eval_P4P_ptC]
  simp only [ptC, Matrix.cons_val_zero, qr, nRr, nZr]
  push_cast; ring

/-- **The node `(1 + E₄)^{−1/2}` at a real point** is `R^{−4}/P₄`. -/
theorem eval_eV4_ptC {a : Fin 6 → ℝ} {u z c s : ℝ} (hx : ∀ i, ‖ptC u z c s 0 0 i‖ ≤ a i)
    (hE4 : PolyExpr.maj a E4P < 1) (hu : |u| ≤ 1 / 4) :
    PolyExprS.eval (ptC u z c s 0 0) eV4 = ((1 / ((1 + u) ^ 4 * P4u u) : ℝ) : ℂ) := by
  have hV : PolyExprS.Valid a eV4 := ⟨PolyExprS.valid_ofPoly _ _, by
    rw [PolyExprS.maj_ofPoly]; exact hE4⟩
  have hr : (AlgHom.id ℂ ℂ) (PolyExprS.eval (ptC u z c s 0 0) (PolyExprS.ofPoly E4P)) =
      (((1 + u) ^ 8 * P4u u ^ 2 - 1 : ℝ) : ℂ) := by
    rw [AlgHom.id_apply, PolyExprS.eval_ofPoly, eval_E4P_ptC]
  obtain ⟨-, hval⟩ := PolyExprS.eval_isqrt_point (AlgHom.id ℂ ℂ) hx hV hr
  rw [AlgHom.id_apply] at hval
  have hP := P4u_pos hu
  have hR : 0 < 1 + u := by linarith [(abs_le.mp hu).1]
  have e : ∀ a b : ℝ, Sub.sub a b = a - b := fun _ _ => rfl
  have e' : ∀ a b : ℝ, Div.div a b = a / b := fun _ _ => rfl
  rw [show eV4 = PolyExprS.isqrt 1 (PolyExprS.ofPoly E4P) from rfl, hval]
  congr 1
  rw [e, e', show (1 : ℝ) + ((1 + u) ^ 8 * P4u u ^ 2 - 1) = ((1 + u) ^ 4 * P4u u) ^ 2 by ring,
    Real.sqrt_sq (by positivity), one_div]

/-- `|B| = √q / R⁴` in the variables of the flow form. -/
def Bmr (R z C S : ℝ) : ℝ := √(qr R z C S) / R ^ 4

/-- **`|B|` in cylindrical coordinates**: `‖field (1/4) (cylPt R φ z)‖ = √q/R⁴`. -/
theorem norm_field_cylPt {R : ℝ} (hR : 0 < R) (φ z : ℝ) :
    ‖field (1 / 4) (cylPt R φ z)‖ = Bmr R z (cos (2 * φ)) (sin (2 * φ)) := by
  have h := Qf_cylPt hR φ z
  rw [Qf] at h
  rw [Bmr, ← Real.sqrt_sq (norm_nonneg _), h, Real.sqrt_div' _ (by positivity),
    show R ^ 8 = (R ^ 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]

/-- **`|B|` at a real point**: the tree `eBm` evaluates to `√q/R⁴`. -/
theorem eval_eBm_ptC {a : Fin 6 → ℝ} {u z c s : ℝ} (hx : ∀ i, ‖ptC u z c s 0 0 i‖ ≤ a i)
    (hE : PolyExpr.maj a EpP < 1) (hE4 : PolyExpr.maj a E4P < 1) (hu : |u| ≤ 1 / 4) :
    PolyExprS.eval (ptC u z c s 0 0) eBm = (Bmr (1 + u) z c s : ℂ) := by
  obtain ⟨hq, hV⟩ := eval_eV_ptC hx hE hu
  have hP := Pu_pos hu
  have hP4 := P4u_pos hu
  have hR : 0 < 1 + u := by linarith [(abs_le.mp hu).1]
  simp only [eBm, PolyExprS.eval, PolyExprS.eval_ofPoly]
  rw [eval_QPP4P_ptC, hV, eval_eV4_ptC hx hE4 hu]
  have hs : 0 < √(qr (1 + u) z c s) := Real.sqrt_pos.2 hq
  have hsq : √(qr (1 + u) z c s) ^ 2 = qr (1 + u) z c s := Real.sq_sqrt hq.le
  have key : qr (1 + u) z c s * Pu u * P4u u * (Wr (1 + u) z c s / Pu u *
      (1 / ((1 + u) ^ 4 * P4u u))) = Bmr (1 + u) z c s := by
    simp only [Bmr, Wr]
    set t := √(qr (1 + u) z c s) with ht
    rw [← hsq]
    field_simp
  rw [← key]
  push_cast
  ring

/-- `|B| ≥ 0`. -/
theorem Bmr_nonneg (R z C S : ℝ) : 0 ≤ Bmr R z C S := by
  unfold Bmr
  rcases le_or_gt R 0 with h | h
  · rcases eq_or_lt_of_le h with h' | h'
    · rw [h']; simp
    · exact div_nonneg (Real.sqrt_nonneg _) (by positivity)
  · positivity

/-- **The node `(1 − λ|B|)^{−1/2}` at a real point.** -/
theorem eval_eN_ptC {a : Fin 6 → ℝ} {u z c s lm : ℝ} (hx : ∀ i, ‖ptC u z c s 0 0 i‖ ≤ a i)
    (hE : PolyExpr.maj a EpP < 1) (hE4 : PolyExpr.maj a E4P < 1)
    (hN : |lm| * PolyExprS.maj a eBm < 1) (hu : |u| ≤ 1 / 4) :
    0 < 1 - lm * Bmr (1 + u) z c s ∧
    PolyExprS.eval (ptC u z c s 0 0) (eN lm) =
      (((√(1 - lm * Bmr (1 + u) z c s))⁻¹ : ℝ) : ℂ) := by
  have hV : PolyExprS.Valid a eV := ⟨PolyExprS.valid_ofPoly _ _, by
    rw [PolyExprS.maj_ofPoly]; exact hE⟩
  have hV4 : PolyExprS.Valid a eV4 := ⟨PolyExprS.valid_ofPoly _ _, by
    rw [PolyExprS.maj_ofPoly]; exact hE4⟩
  have hB : PolyExprS.Valid a eBm := ⟨PolyExprS.valid_ofPoly _ _, hV, hV4⟩
  have hNv : PolyExprS.Valid a (eN lm) := ⟨⟨trivial, hB⟩, by
    simp only [PolyExprS.maj, norm_neg, Complex.norm_real, Real.norm_eq_abs]; exact hN⟩
  have hr : (AlgHom.id ℂ ℂ) (PolyExprS.eval (ptC u z c s 0 0)
      (.mul (.const (-(lm : ℂ))) eBm)) = ((-lm * Bmr (1 + u) z c s : ℝ) : ℂ) := by
    rw [AlgHom.id_apply]
    simp only [PolyExprS.eval, Algebra.algebraMap_self, RingHom.id_apply,
      eval_eBm_ptC hx hE hE4 hu]
    push_cast; ring
  obtain ⟨hpos, hval⟩ := PolyExprS.eval_isqrt_point (AlgHom.id ℂ ℂ) hx hNv hr
  rw [AlgHom.id_apply] at hval
  have e : ∀ a b : ℝ, Mul.mul a b = a * b := fun _ _ => rfl
  rw [e] at hpos hval
  refine ⟨by linarith, ?_⟩
  rw [show eN lm = PolyExprS.isqrt 1 (.mul (.const (-(lm : ℂ))) eBm) from rfl, hval]
  congr 3; ring

/-- The scalar `F = (1 − λ|B|/2)/√(1 − λ|B|)` of the `μ > 0` passing field. -/
def Fr (lm R z C S : ℝ) : ℝ := (1 - lm * Bmr R z C S / 2) / √(1 - lm * Bmr R z C S)

/-- **Sanity**: `F = 1` for `λ = 0`. -/
theorem Fr_zero (R z C S : ℝ) : Fr 0 R z C S = 1 := by simp [Fr]

/-- **`F` at a real point.** -/
theorem eval_eF_ptC {a : Fin 6 → ℝ} {u z c s lm : ℝ} (hx : ∀ i, ‖ptC u z c s 0 0 i‖ ≤ a i)
    (hE : PolyExpr.maj a EpP < 1) (hE4 : PolyExpr.maj a E4P < 1)
    (hN : |lm| * PolyExprS.maj a eBm < 1) (hu : |u| ≤ 1 / 4) :
    PolyExprS.eval (ptC u z c s 0 0) (eF lm) = (Fr lm (1 + u) z c s : ℂ) := by
  obtain ⟨-, hNe⟩ := eval_eN_ptC hx hE hE4 hN hu
  simp only [eF, PolyExprS.eval, Algebra.algebraMap_self, RingHom.id_apply, hNe,
    eval_eBm_ptC hx hE hE4 hu, Fr]
  push_cast; ring

/-- **`D̃` of the `μ > 0` passing field at a valid real point**: `gcDr (ρ F)`. -/
theorem eval_gcDM_ptC (ρ : ℝ) {a : Fin 6 → ℝ} {u z c s lm : ℝ}
    (hx : ∀ i, ‖ptC u z c s 0 0 i‖ ≤ a i) (hE : PolyExpr.maj a EpP < 1)
    (hE4 : PolyExpr.maj a E4P < 1) (hN : |lm| * PolyExprS.maj a eBm < 1) (hu : |u| ≤ 1 / 4) :
    PolyExprS.eval (ptC u z c s 0 0) (gcDM ρ lm) =
      (gcDr (ρ * Fr lm (1 + u) z c s) (1 + u) z c s : ℂ) := by
  obtain ⟨h0, h1, h2, h3, -⟩ := eval_parts_ptC u z c s
  simp only [gcDM, eYD, eW3, eKD, PolyExprS.eval, PolyExprS.eval_ofPoly, eval_eW_ptC hx hE hu,
    eval_eF_ptC hx hE hE4 hN hu, h0, h1, h2, h3, eval_Dp_ptC, eval_nRp_ptC, eval_nZp_ptC,
    Algebra.algebraMap_self, RingHom.id_apply, gcDr, KDr, nRr, nZr]
  push_cast; ring

/-- **`ñ_R` of the `μ > 0` passing field at a valid real point**: `gcNRr (ρ F)`. -/
theorem eval_gcNRM_ptC (ρ : ℝ) {a : Fin 6 → ℝ} {u z c s lm : ℝ}
    (hx : ∀ i, ‖ptC u z c s 0 0 i‖ ≤ a i) (hE : PolyExpr.maj a EpP < 1)
    (hE4 : PolyExpr.maj a E4P < 1) (hN : |lm| * PolyExprS.maj a eBm < 1) (hu : |u| ≤ 1 / 4) :
    PolyExprS.eval (ptC u z c s 0 0) (gcNRM ρ lm) =
      (gcNRr (ρ * Fr lm (1 + u) z c s) (1 + u) z c s : ℂ) := by
  obtain ⟨h0, -, -, h3, h4⟩ := eval_parts_ptC u z c s
  simp only [gcNRM, eYR, eW3, eKR, PolyExprS.eval, PolyExprS.eval_ofPoly, eval_eW_ptC hx hE hu,
    eval_eF_ptC hx hE hE4 hN hu, h0, h3, h4, eval_Dp_ptC, eval_nRp_ptC, eval_nZp_ptC,
    Algebra.algebraMap_self, RingHom.id_apply, gcNRr, KRr, nRr, nZr]
  push_cast; ring

/-- **`ñ_z` of the `μ > 0` passing field at a valid real point**: `gcNZr (ρ F)`. -/
theorem eval_gcNZM_ptC (ρ : ℝ) {a : Fin 6 → ℝ} {u z c s lm : ℝ}
    (hx : ∀ i, ‖ptC u z c s 0 0 i‖ ≤ a i) (hE : PolyExpr.maj a EpP < 1)
    (hE4 : PolyExpr.maj a E4P < 1) (hN : |lm| * PolyExprS.maj a eBm < 1) (hu : |u| ≤ 1 / 4) :
    PolyExprS.eval (ptC u z c s 0 0) (gcNZM ρ lm) =
      (gcNZr (ρ * Fr lm (1 + u) z c s) (1 + u) z c s : ℂ) := by
  obtain ⟨h0, h1, h2, -, h4⟩ := eval_parts_ptC u z c s
  simp only [gcNZM, eYZ, eW3, eKZ, PolyExprS.eval, PolyExprS.eval_ofPoly, eval_eW_ptC hx hE hu,
    eval_eF_ptC hx hE hE4 hN hu, h0, h1, h2, h4, eval_Dp_ptC, eval_nRp_ptC, eval_nZp_ptC,
    Algebra.algebraMap_self, RingHom.id_apply, gcNZr, KZr, nRr, nZr]
  push_cast; ring

end PlasmaLean.Design.RationalStellaratorGC
