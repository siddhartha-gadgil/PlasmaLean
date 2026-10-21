/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2FluxLabels

/-!
# Landreman family 2: the coarea formula identifies the area element `JacR dχ dζ`

For family 2 (`ε = 1/4`, `S = 4`, `λ > 0`) and every continuous `f : ℝ³ → ℝ`,

`d/dψ ∫_{x ∈ R, ψ(x) ≤ ψ} f dx = ∫∫ f(x(ψ, χ, ζ)) JacR dχ dζ`  (`hasDerivAt_integral_plasmaPsi`)

on every surface `0 < ψ < (47/50)²/2`. The left side is the coarea density `∮ f dS/|∇ψ|`, so the
measure `JacR dχ dζ` used in the Mercier surface integrals of `family2Data` is the surface
measure `dS/|∇ψ|` (the area element of paper (3.18) is derived, not assumed). Proof: change of
variables with the coordinate map (`integral_plasma`), Fubini on the coordinate box
(`integral_coordDom_eq`), continuity of the angular integral (joint continuity of the closed
forms on `k² < 1`, `continuousOn_jac3`) and the fundamental theorem of calculus, then the chain
rule `k = √(2ψ)`. The case `f = 1` gives `V'(ψ) = Z E/(2λ)` (`hasDerivAt_volume_plasmaPsi`).
-/

public section
noncomputable section

namespace PlasmaLean.Design.LandremanFamily2Coarea

open Real Set MeasureTheory Filter Topology WithLp
open PlasmaLean.Fields PlasmaLean.Design.LandremanFamily2
open PlasmaLean.Design.LandremanFamily2Surface PlasmaLean.Design.LandremanFamily2Rotated
open PlasmaLean.Design.LandremanFamily2Coords PlasmaLean.Design.LandremanFamily2Labels
open PlasmaLean.Design.LandremanFamily2FluxLabels

/-! ## Joint continuity of the closed forms -/

/-- The parameter region `k² < 1` in the coordinates `q = (k, χ, ζ)`. -/
@[expose] def S3 : Set (ℝ × ℝ × ℝ) := {q | q.1 ^ 2 < 1}

/-- The coordinate point `x(k, χ, ζ)` as a function of a triple. -/
@[expose] def X3 (lam : ℝ) (q : ℝ × ℝ × ℝ) : Space := surfPt (1 / 4) 4 lam q.1 q.2.1 q.2.2

/-- The area element `JacR` as a function of a triple. -/
@[expose] def J3 (lam : ℝ) (q : ℝ × ℝ × ℝ) : ℝ :=
  JacR lam q.1 (Real.sin q.2.1) (Real.cos q.2.1) (Real.sin (2 * q.2.2)) (Real.cos (2 * q.2.2))

section Cont
variable {lam : ℝ}

/-- Continuity of `sin(σ - S)` on `k² < 1`. -/
theorem continuousOn_sA3 : ContinuousOn
    (fun q : ℝ × ℝ × ℝ => sA (1 / 4) q.1 (Real.sin q.2.1) (Real.cos q.2.1) (Real.sin (2 * q.2.2)))
    S3 := by
  have hn : Continuous fun q : ℝ × ℝ × ℝ =>
      cc q.1 (Real.sin q.2.1) * chc (1 / 4) (Real.sin (2 * q.2.2)) * Xc q.1 (Real.cos q.2.1) +
        Yc q.1 (Real.sin q.2.1) * shc (1 / 4) (Real.sin (2 * q.2.2)) *
          Tc (1 / 4) q.1 (Real.sin (2 * q.2.2)) := by
    simp only [cc, chc, shc, Xc, Yc, Tc, nuc]; fun_prop
  have hd : Continuous fun q : ℝ × ℝ × ℝ =>
      T0c (1 / 4) q.1 (Real.sin q.2.1) (Real.sin (2 * q.2.2)) := by
    simp only [T0c, chc, Yc, nuc]; fun_prop
  exact hn.continuousOn.div hd.continuousOn fun q hq =>
    (T0_pos (Real.sin_sq_add_cos_sq q.2.1) hq).ne'

/-- Continuity of `σ` on `k² < 1`. -/
theorem continuousOn_sig3 : ContinuousOn
    (fun q : ℝ × ℝ × ℝ => sigc (1 / 4) 4 q.1 (Real.sin q.2.1) (Real.cos q.2.1)
      (Real.sin (2 * q.2.2))) S3 :=
  continuousOn_const.add (Real.continuous_arcsin.comp_continuousOn continuousOn_sA3)

/-- Continuity of the coordinate point on `k² < 1`. -/
theorem continuousOn_X3 : ContinuousOn (X3 lam) S3 := by
  have hs := continuousOn_sig3
  have ha : ContinuousOn (fun q : ℝ × ℝ × ℝ => aC (1 / 4) (sigc (1 / 4) 4 q.1 (Real.sin q.2.1)
      (Real.cos q.2.1) (Real.sin (2 * q.2.2)))) S3 := by
    unfold aC hC
    exact (by fun_prop : Continuous fun s : ℝ => √((√(4 * s ^ 2 + (1 / 4) ^ 2) - 1 / 4) / 2))
      |>.comp_continuousOn hs
  have hb : ContinuousOn (fun q : ℝ × ℝ × ℝ => bC (1 / 4) (sigc (1 / 4) 4 q.1 (Real.sin q.2.1)
      (Real.cos q.2.1) (Real.sin (2 * q.2.2)))) S3 := by
    unfold bC hC
    exact (by fun_prop : Continuous fun s : ℝ => √((√(4 * s ^ 2 + (1 / 4) ^ 2) + 1 / 4) / 2))
      |>.comp_continuousOn hs
  refine (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.2 fun i => ?_)
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    exact ha.mul (by fun_prop : Continuous fun q : ℝ × ℝ × ℝ => Real.cos q.2.2).continuousOn
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact hb.mul (by fun_prop : Continuous fun q : ℝ × ℝ × ℝ => Real.sin q.2.2).continuousOn
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    exact (by fun_prop : Continuous fun q : ℝ × ℝ × ℝ =>
      -Real.arcsin (q.1 * Real.sin q.2.1) / lam).continuousOn

/-- Continuity of the area element on `k² < 1` (`λ ≠ 0`). -/
theorem continuousOn_J3 (hl : lam ≠ 0) : ContinuousOn (J3 lam) S3 := by
  have hs := continuousOn_sig3
  have hh : ContinuousOn (fun q : ℝ × ℝ × ℝ => hc (1 / 4) 4 q.1 (Real.sin q.2.1)
      (Real.cos q.2.1) (Real.sin (2 * q.2.2))) S3 := by
    unfold hc
    exact (by fun_prop : Continuous fun s : ℝ => √(4 * s ^ 2 + (1 / 4) ^ 2)).comp_continuousOn hs
  have hT : Continuous fun q : ℝ × ℝ × ℝ => Tc (1 / 4) q.1 (Real.sin (2 * q.2.2)) := by
    simp only [Tc, chc, nuc]; fun_prop
  have hcc : Continuous fun q : ℝ × ℝ × ℝ => cc q.1 (Real.sin q.2.1) := by
    simp only [cc, Yc]; fun_prop
  have hG : ContinuousOn (fun q : ℝ × ℝ × ℝ => Gc (1 / 4) 4 q.1 (Real.sin q.2.1)
      (Real.cos q.2.1) (Real.sin (2 * q.2.2)) (Real.cos (2 * q.2.2))) S3 := by
    unfold Gc
    exact (hh.add (by fun_prop : Continuous fun q : ℝ × ℝ × ℝ =>
      1 / 4 * Real.cos (2 * q.2.2)).continuousOn).div_const 2
  refine hG.div (((continuousOn_const.mul hh).mul hT.continuousOn).mul hcc.continuousOn)
    fun q hq => ?_
  have h1 := hc_pos (ε := 1 / 4) (k := q.1) (s1 := Real.sin q.2.1) (c1 := Real.cos q.2.1)
    (s2 := Real.sin (2 * q.2.2)) (by norm_num : (2 : ℝ) ≤ 4)
  have h2 := T_pos (ε := 1 / 4) (s2 := Real.sin (2 * q.2.2)) (show q.1 ^ 2 < 1 from hq)
  have h3 := cc_pos (k := q.1) (Real.sin_sq_add_cos_sq q.2.1) (show q.1 ^ 2 < 1 from hq)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hl h1.ne') h2.ne') h3.ne'

end Cont

/-! ## Clamped integrand and its angular integral -/

/-- Clamp of `k` to `[0, 47/50]`. -/
@[expose] def kcl (k : ℝ) : ℝ := max 0 (min k (47 / 50))

/-- The clamp is continuous. -/
theorem continuous_kcl : Continuous kcl := by unfold kcl; fun_prop

/-- The clamp is the identity on `[0, 47/50]`. -/
theorem kcl_eq {k : ℝ} (h0 : 0 ≤ k) (h1 : k ≤ 47 / 50) : kcl k = k := by
  unfold kcl; rw [min_eq_left h1, max_eq_right h0]

/-- The clamp lies in `k² < 1`. -/
theorem kcl_sq (k : ℝ) : kcl k ^ 2 < 1 := by
  have h0 : 0 ≤ kcl k := le_max_left _ _
  have h1 : kcl k ≤ 47 / 50 := max_le (by norm_num) (min_le_right _ _)
  nlinarith

/-- The clamped coarea integrand `k JacR f(x)` (agrees with it for `0 ≤ k ≤ 47/50`). -/
@[expose] def Gk (lam : ℝ) (f : Space → ℝ) (q : ℝ × ℝ × ℝ) : ℝ :=
  kcl q.1 * J3 lam (kcl q.1, q.2) * f (X3 lam (kcl q.1, q.2))

/-- The clamped integrand is continuous for continuous `f`. -/
theorem continuous_Gk {lam : ℝ} (hl : lam ≠ 0) {f : Space → ℝ} (hf : Continuous f) :
    Continuous (Gk lam f) := by
  have hm : Continuous fun q : ℝ × ℝ × ℝ => (kcl q.1, q.2) :=
    (continuous_kcl.comp continuous_fst).prodMk continuous_snd
  have hS : ∀ q : ℝ × ℝ × ℝ, (kcl q.1, q.2) ∈ S3 := fun q => kcl_sq q.1
  exact ((continuous_kcl.comp continuous_fst).mul ((continuousOn_J3 hl).comp_continuous hm hS)).mul
    (hf.comp (continuousOn_X3.comp_continuous hm hS))

/-- `Φ_f(k) = ∫∫ (k JacR f)(k, χ, ζ) dζ dχ` (clamped). -/
@[expose] def PhiK (lam : ℝ) (f : Space → ℝ) (k : ℝ) : ℝ :=
  ∫ χ in (-π)..π, ∫ ζ in (-π)..π, Gk lam f (k, χ, ζ)

/-- `Φ_f` is continuous for continuous `f`. -/
theorem continuous_PhiK {lam : ℝ} (hl : lam ≠ 0) {f : Space → ℝ} (hf : Continuous f) :
    Continuous (PhiK lam f) := by
  have h1 : Continuous fun x : ℝ × ℝ => ∫ ζ in (-π)..π, Gk lam f (x.1, x.2, ζ) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (x : ℝ × ℝ) ζ => Gk lam f (x.1, x.2, ζ))
      ((continuous_Gk hl hf).comp (by fun_prop)) _ _
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun k χ => ∫ ζ in (-π)..π, Gk lam f (k, χ, ζ)) (h1.comp (by fun_prop)) _ _

/-! ## Change of variables, Fubini and the coarea formula -/

section Coarea
variable {lam k₀ : ℝ}

/-- **Change of variables** for integrals over the plasma: `∫_{plasma} f = ∫_box k JacR f(x)`. -/
theorem integral_plasma (hl : 0 < lam) (f : Space → ℝ) (hk0 : 0 ≤ k₀) (hk₀ : k₀ < 19 / 20) :
    ∫ x in plasma lam k₀, f x = ∫ p in coordDom k₀, p 0 * JacP lam p * f (coordMap lam p) := by
  rw [setIntegral_congr_set (plasma_ae_eq_shell hl.ne' k₀), ← image_coordMap hl hk0 hk₀.le,
    integral_image_eq_integral_abs_det_fderiv_smul volume (measurableSet_coordDom k₀)
      (fun p hp => (hasFDerivAt_coordMap (lam := lam) (good_of_mem hk₀.le hp)).hasFDerivWithinAt)
      (injOn_coordMap hl hk₀.le)]
  refine setIntegral_congr_fun (measurableSet_coordDom k₀) fun p hp => ?_
  have hg := good_of_mem hk₀.le hp
  rw [coordDeriv_det hl hg (lt_of_le_of_lt hp.1.2 hk₀),
    abs_of_nonneg (mul_nonneg hg.1.le (JacP_pos hl hg).le), smul_eq_mul]

/-- **Fubini on the coordinate box**: `∫_box k JacR f = ∫₀^{k₀} Φ_f(k) dk` (`k₀ ≤ 47/50`). -/
theorem integral_coordDom_eq (hl : 0 < lam) {f : Space → ℝ} (hf : Continuous f)
    (hk0 : 0 ≤ k₀) (hk₀ : k₀ ≤ 47 / 50) :
    ∫ p in coordDom k₀, p 0 * JacP lam p * f (coordMap lam p) =
      ∫ k in (0 : ℝ)..k₀, PhiK lam f k := by
  have hpi : -π ≤ π := by linarith [Real.pi_pos]
  rw [setIntegral_congr_fun (measurableSet_coordDom k₀) (g := fun p => Gk lam f (toTriple p))
    (fun p hp => by
      simp only [Gk, toTriple_apply, kcl_eq hp.1.1.le (hp.1.2.trans hk₀)]
      rfl)]
  have hD : coordDom k₀ = toTriple ⁻¹' (Ioc 0 k₀ ×ˢ (Ioc (-π) π ×ˢ Ioc (-π) π)) := by
    ext p; simp [coordDom, toTriple_apply]
  rw [hD, measurePreserving_toTriple.setIntegral_preimage_emb toTriple.measurableEmbedding]
  have hint : IntegrableOn (Gk lam f) (Ioc 0 k₀ ×ˢ (Ioc (-π) π ×ˢ Ioc (-π) π)) :=
    ((continuous_Gk hl.ne' hf).continuousOn.integrableOn_compact
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))).mono_set
      (prod_mono Ioc_subset_Icc_self (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self))
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [setIntegral_prod _ hint, intervalIntegral.integral_of_le hk0]
  refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
  have hint2 : IntegrableOn (fun y : ℝ × ℝ => Gk lam f (x, y)) (Ioc (-π) π ×ˢ Ioc (-π) π) :=
    (((continuous_Gk hl.ne' hf).comp (Continuous.prodMk_right x)).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [Measure.volume_eq_prod] at hint2
  rw [Measure.volume_eq_prod, setIntegral_prod _ hint2, PhiK, intervalIntegral.integral_of_le hpi]
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  rw [intervalIntegral.integral_of_le hpi]

/-- `Φ_f(k) = k ∫∫ f(x) JacR dζ dχ` for `0 ≤ k ≤ 47/50`. -/
theorem PhiK_eq (f : Space → ℝ) {k : ℝ} (h0 : 0 ≤ k) (h1 : k ≤ 47 / 50) :
    PhiK lam f k = k * ∫ χ in (-π)..π, ∫ ζ in (-π)..π,
      f (surfPt (1 / 4) 4 lam k χ ζ) *
        JacR lam k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) := by
  unfold PhiK Gk
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun χ _ => ?_
  simp only
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun ζ _ => ?_
  simp only [kcl_eq h0 h1, J3, X3]
  ring

/-- **Coarea formula in `k`**: `d/dk ∫_{plasma k} f = Φ_f(k)` for continuous `f`,
`0 < k < 47/50`. -/
theorem hasDerivAt_integral_plasma (hl : 0 < lam) {f : Space → ℝ} (hf : Continuous f) {k : ℝ}
    (hk : k ∈ Ioo (0 : ℝ) (47 / 50)) :
    HasDerivAt (fun k => ∫ x in plasma lam k, f x) (PhiK lam f k) k := by
  have hF := ((continuous_PhiK hl.ne' hf).integral_hasStrictDerivAt 0 k).hasDerivAt
  refine hF.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hk.1 hk.2] with x hx
  rw [integral_plasma hl f hx.1.le (by linarith [hx.2]),
    integral_coordDom_eq hl hf hx.1.le hx.2.le]

/-- The plasma `{x ∈ R | ψ(x) ≤ ψ₀}` labelled by `ψ₀`. -/
@[expose] def plasmaPsi (lam ψ₀ : ℝ) : Set Space :=
  {x | x ∈ R (1 / 4) 4 lam ∧ psi (1 / 4) 4 lam x ≤ ψ₀}

/-- `plasmaPsi ψ₀ = plasma √(2ψ₀)`. -/
theorem plasmaPsi_eq {ψ₀ : ℝ} (h : 0 ≤ ψ₀) : plasmaPsi lam ψ₀ = plasma lam √(2 * ψ₀) := by
  ext x
  simp only [plasmaPsi, plasma, mem_ofPred_eq, Real.sq_sqrt (by linarith : 0 ≤ 2 * ψ₀)]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

/-- **Coarea formula** for family 2: for continuous `f` and `0 < ψ < (47/50)²/2`,
`d/dψ ∫_{x ∈ R, ψ(x) ≤ ψ} f dx = ∫∫ f(x(ψ, χ, ζ)) JacR dζ dχ` (`k = √(2ψ)`), i.e. `JacR dχ dζ` is
the coarea measure `dS/|∇ψ|` of the flux surface. -/
theorem hasDerivAt_integral_plasmaPsi (hl : 0 < lam) {f : Space → ℝ} (hf : Continuous f)
    {ψ : ℝ} (hψ : ψ ∈ Ioo (0 : ℝ) ((47 / 50) ^ 2 / 2)) :
    HasDerivAt (fun ψ => ∫ x in plasmaPsi lam ψ, f x)
      (∫ χ in (-π)..π, ∫ ζ in (-π)..π, f (surfPt (1 / 4) 4 lam √(2 * ψ) χ ζ) *
        JacR lam √(2 * ψ) (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ))) ψ := by
  have hk0 : 0 < √(2 * ψ) := Real.sqrt_pos.2 (by linarith [hψ.1])
  have hk1 : √(2 * ψ) < 47 / 50 := by
    rw [show (47 / 50 : ℝ) = √((47 / 50) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by linarith [hψ.1]) (by linarith [hψ.2])
  have hsq : HasDerivAt (fun ψ => √(2 * ψ)) (2 / (2 * √(2 * ψ))) ψ := by
    simpa using ((hasDerivAt_id ψ).const_mul 2).sqrt (by simp only [id]; linarith [hψ.1])
  have h := (hasDerivAt_integral_plasma hl hf ⟨hk0, hk1⟩).comp ψ hsq
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [Ioo_mem_nhds hψ.1 hψ.2] with x hx
    simp only [Function.comp_apply]
    rw [plasmaPsi_eq hx.1.le]
  · rw [PhiK_eq f hk0.le hk1.le]
    field_simp

/-- `f = 1`: **`V'(ψ) = Z E/(2λ)`** for the Lebesgue volume of the plasma. -/
theorem hasDerivAt_volume_plasmaPsi (hl : 0 < lam) {ψ : ℝ}
    (hψ : ψ ∈ Ioo (0 : ℝ) ((47 / 50) ^ 2 / 2)) :
    HasDerivAt (fun ψ => ∫ _ in plasmaPsi lam ψ, (1 : ℝ))
      (Zint (1 / 4) √(2 * ψ) * Eint √(2 * ψ) / (2 * lam)) ψ := by
  have hk0 : 0 < √(2 * ψ) := Real.sqrt_pos.2 (by linarith [hψ.1])
  have hk1 : √(2 * ψ) ^ 2 < 1 := by
    rw [Real.sq_sqrt (by linarith [hψ.1])]; nlinarith [hψ.2]
  have h := hasDerivAt_integral_plasmaPsi hl (f := fun _ => 1) continuous_const hψ
  simp only [one_mul] at h
  rwa [integral_JacR hl.ne' hk0 hk1] at h

end Coarea

end PlasmaLean.Design.LandremanFamily2Coarea
