/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCTube
public import PlasmaLean.Design.RationalStellaratorGCStar
public import PlasmaLean.Certificates.KernelFact

/-!
# All-time confinement of the field lines of the guiding-centre field (`ρ_s = 1/256`)

**Main theorem** (`rationalStellarator_gc_field_confined_forever`): there is a torus profile
`ρ(θ, φ)` with `0.03 ≤ ρ ≤ 0.253` (distance from the exact magnetic axis `R = 1, z = 0` of
`field (1/4)`) such that from every point on the axis or strictly inside the torus `rt < ρ(θs, φs)`
there is exactly one two-sided field line of the guiding-centre field `gcField (1/256)` (it exists
for all time), and every field line of `gcField (1/256)` starting there stays inside the torus —
within distance `0.253` of the axis — **for all time**, forward and backward.

The torus is the exact invariant torus of rotational transform `ι = (75 + √5)/562` of the
guiding-centre flow form (`gc_exact_torus`, KAM). Ingredients:

* `gc_exact_torus_data`: the exact torus as real `C²` functions `Rk = Rof u`, `zk = Zof z`,
  `10⁻¹²`-close to `K₀` in `C¹`, solving the flow form in the real form
  `D̃ (∂_φ K + ι ∂_θ K) = (ñ_R, ñ_z)` (`gcDr`, `gcNRr`, `gcNZr` of
  `Design/RationalStellaratorGCCyl`, via `eval_gcD_ptC`), with `D̃ ≥ 0.6` on it (from the certified
  bound `‖D̃ − d₀‖ ≤ 0.3302`, `Bd_Ddev`) and `q > 0`;
* `cRTZ_gcField`: the cylindrical components of `gcField ρ` are `(ñ_R, D̃, ñ_z)/R⁴`
  (`gcField_cylPt_real`), so the torus is a flow torus of `gcField (1/256)` (`gc_flowTorus`);
* the star-shapedness certificate (`gc_radial_ge`, `gc_winding_ge`,
  `Design/RationalStellaratorGCStar`) and the torus bounds of `K₀` (`Bd_u₀G`, …) give
  star-shapedness, positive winding and `0.03 ≤ rt ≤ 0.253` for the exact torus;
* `gcField (1/256)` is `C²` on `{r₂ > 0, B ≠ 0}` (`gcField_contDiffOn`), which contains the tube
  `rt ≤ 0.3` (`norm_field_ge`); `FlowTorus.confined_existsUnique` concludes.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open Real Set PlasmaLean.Fields PlasmaLean.Design.RationalStellarator PlasmaLean.Design.KamTorusA
  PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton WEll1Z2 WithLp

/-! ## The cylindrical components of `gcField` -/

/-- **Cylindrical components of the guiding-centre field**: for `R > 0`, `q > 0`,
`c_R = ñ_R/R⁴`, `c_T = D̃/R⁴`, `c_z = ñ_z/R⁴`. -/
theorem cRTZ_gcField (ρ : ℝ) {R : ℝ} (hR : 0 < R) (φ z : ℝ)
    (hq : 0 < qr R z (cos (2 * φ)) (sin (2 * φ))) :
    cR (gcField ρ) R φ z = gcNRr ρ R z (cos (2 * φ)) (sin (2 * φ)) / R ^ 4 ∧
      cT (gcField ρ) R φ z = gcDr ρ R z (cos (2 * φ)) (sin (2 * φ)) / R ^ 4 ∧
      cZ (gcField ρ) R φ z = gcNZr ρ R z (cos (2 * φ)) (sin (2 * φ)) / R ^ 4 := by
  have hcs := cos_sq_add_sin_sq φ
  have hR0 : R ≠ 0 := hR.ne'
  simp only [cR, cT, cZ, gcField_cylPt_real ρ hR φ z hq, eRv, ePv, eZv, inner_toLp3]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, mul_zero,
    add_zero, mul_one, zero_add]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination gcNRr ρ R z (cos (2 * φ)) (sin (2 * φ)) / R ^ 4 * hcs
  · field_simp
    linear_combination R * gcDr ρ R z (cos (2 * φ)) (sin (2 * φ)) * hcs
  · rfl

/-! ## The exact guiding-centre torus -/

/-- Pointwise bound of the real torus from a strip bound of `u`. -/
theorem abs_Rof_sub_one_le {u : FA} {ρ B : ℝ} (hρ : 0 ≤ ρ) (h : Bd ρ u B) (θ φ : ℝ) :
    |Rof u θ φ - 1| ≤ B := by
  rw [Rof, add_sub_cancel_left]
  exact (Complex.abs_re_le_norm _).trans (KamNewton.norm_eval_le_of_Bd hρ h θ (psi φ))

/-- Pointwise bound of the real height from a strip bound of `z`. -/
theorem abs_Zof_le {z : FA} {ρ B : ℝ} (hρ : 0 ≤ ρ) (h : Bd ρ z B) (θ φ : ℝ) :
    |Zof z θ φ| ≤ B :=
  (Complex.abs_re_le_norm _).trans (KamNewton.norm_eval_le_of_Bd hρ h θ (psi φ))

/-- Pointwise closeness of real parts from a strip bound of the difference. -/
theorem abs_re_sub_le {x y : FA} {ρ B : ℝ} (hρ : 0 ≤ ρ) (h : Bd ρ (x - y) B) (θ ψ : ℝ) :
    |(WEll1Z2.eval x θ ψ).re - (WEll1Z2.eval y θ ψ).re| ≤ B := by
  have h1 := KamNewton.norm_eval_le_of_Bd hρ h θ ψ
  rw [eval_sub'] at h1
  have h2 := (Complex.abs_re_le_norm _).trans h1
  simpa using h2

/-- **The exact guiding-centre torus in real form** (`ρ_s = 1/256`): `C²` periodic functions
`Rk, zk` of `(θ, φ)` solving `D̃ (∂_φ K + ι ∂_θ K) = (ñ_R, ñ_z)` with `ι = (75 + √5)/562`, with
`D̃ ≥ 0.6`, `q > 0` on the torus, and `10⁻¹²`-close in `C¹` to the certified torus `K₀`. -/
theorem gc_exact_torus_data : ∃ Rk zk : ℝ → ℝ → ℝ,
    ContDiff ℝ 2 (fun p : ℝ × ℝ => Rk p.1 p.2) ∧ ContDiff ℝ 2 (fun p : ℝ × ℝ => zk p.1 p.2) ∧
    (∀ θ φ, Rk (θ + 2 * π) φ = Rk θ φ) ∧ (∀ θ φ, zk (θ + 2 * π) φ = zk θ φ) ∧
    (∀ θ φ, Rk θ (φ + π) = Rk θ φ) ∧ (∀ θ φ, zk θ (φ + π) = zk θ φ) ∧
    (∀ θ φ, gcDr (1 / 256) (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) *
        (deriv (fun φ' => Rk θ φ') φ + iota * deriv (fun θ' => Rk θ' φ) θ) =
      gcNRr (1 / 256) (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ))) ∧
    (∀ θ φ, gcDr (1 / 256) (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) *
        (deriv (fun φ' => zk θ φ') φ + iota * deriv (fun θ' => zk θ' φ) θ) =
      gcNZr (1 / 256) (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ))) ∧
    (∀ θ φ, 3 / 5 ≤ gcDr (1 / 256) (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ))) ∧
    (∀ θ φ, 0 < qr (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ))) ∧
    (∀ θ φ, |Rk θ φ - Rof u₀G θ φ| ≤ μG) ∧ (∀ θ φ, |zk θ φ - Zof z₀G θ φ| ≤ μG) ∧
    (∀ θ φ, |deriv (fun θ' => Rk θ' φ) θ - (WEll1Z2.eval (dTh u₀G) θ (psi φ)).re| ≤ μG) ∧
    (∀ θ φ, |deriv (fun θ' => zk θ' φ) θ - (WEll1Z2.eval (dTh z₀G) θ (psi φ)).re| ≤ μG) := by
  obtain ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩ := gc_exact_torus
  have hx := norm_xK_le hC
  have hv := gc_valid_res aRes_le.1 aRes_le.2
  have hE := gc_maj_E_lt aRes_le.1 aRes_le.2
  have hn := gc_noW (1 / 256)
  have h0 : (0 : ℝ) ≤ KamTorusA.rA / 7 := by norm_num [KamTorusA.rA]
  have h7 : KamTorusA.rA / 7 ≤ KamTorusA.rA := by norm_num [KamTorusA.rA]
  -- pointwise bounds of the torus variables
  have tu : Bd (KamTorusA.rA / 7) u auG := by
    have := hC.du.add (Bd_u₀G.strip h7); rw [sub_add_cancel] at this
    exact this.le (by rw [auG]; linarith)
  have tz : Bd (KamTorusA.rA / 7) z azG := by
    have := hC.dz.add (Bd_z₀G.strip h7); rw [sub_add_cancel] at this
    exact this.le (by rw [azG]; linarith)
  have hpt : ∀ θ φ, ∀ i, ‖ptC (Rof u θ φ - 1) (Zof z θ φ) (cos (2 * φ)) (sin (2 * φ)) 0 0 i‖ ≤
      aRes i := by
    intro θ φ i
    fin_cases i
    · change ‖((Rof u θ φ - 1 : ℝ) : ℂ)‖ ≤ auG
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_Rof_sub_one_le h0 tu θ φ
    · change ‖((Zof z θ φ : ℝ) : ℂ)‖ ≤ azG
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_Zof_le h0 tz θ φ
    · change ‖((cos (2 * φ) : ℝ) : ℂ)‖ ≤ 1
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_cos_le_one _
    · change ‖((sin (2 * φ) : ℝ) : ℂ)‖ ≤ 1
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_sin_le_one _
    · change ‖((0 : ℝ) : ℂ)‖ ≤ aLRG
      rw [Complex.ofReal_zero, norm_zero]; norm_num [aLRG, μG]
    · change ‖((0 : ℝ) : ℂ)‖ ≤ aLzG
      rw [Complex.ofReal_zero, norm_zero]; norm_num [aLzG, μG]
  have hu4 : ∀ θ φ, |Rof u θ φ - 1| ≤ 1 / 4 := fun θ φ =>
    (abs_Rof_sub_one_le h0 tu θ φ).trans (by norm_num [auG, μG])
  have e1 : ∀ θ φ, 1 + (Rof u θ φ - 1) = Rof u θ φ := fun _ _ => by ring
  -- the flow-form expressions at the torus points
  have hD : ∀ θ φ, PolyExprS.eval (gcPt (Rof u θ φ) (Zof z θ φ) φ) (gcD (1 / 256)) =
      (gcDr (1 / 256) (Rof u θ φ) (Zof z θ φ) (cos (2 * φ)) (sin (2 * φ)) : ℂ) := fun θ φ => by
    rw [gcPt, eval_gcD_ptC _ (hpt θ φ) hE (hu4 θ φ), e1]
  have hNR : ∀ θ φ, PolyExprS.eval (gcPt (Rof u θ φ) (Zof z θ φ) φ) (gcNR (1 / 256)) =
      (gcNRr (1 / 256) (Rof u θ φ) (Zof z θ φ) (cos (2 * φ)) (sin (2 * φ)) : ℂ) := fun θ φ => by
    rw [gcPt, eval_gcNR_ptC _ (hpt θ φ) hE (hu4 θ φ), e1]
  have hNZ : ∀ θ φ, PolyExprS.eval (gcPt (Rof u θ φ) (Zof z θ φ) φ) (gcNZ (1 / 256)) =
      (gcNZr (1 / 256) (Rof u θ φ) (Zof z θ φ) (cos (2 * φ)) (sin (2 * φ)) : ℂ) := fun θ φ => by
    rw [gcPt, eval_gcNZ_ptC _ (hpt θ φ) hE (hu4 θ φ), e1]
  -- the inputs of the low-resolution chain (for the bound on `D̃`)
  have hrpos : 0 < KamTorusA.rA / 7 := by norm_num [KamTorusA.rA]
  have hq7 : Real.exp (KamTorusA.rA / 7) ≤ (74315 : ℕ) / 2 ^ 16 :=
    (Real.exp_le_exp.2 h7).trans exp_rA_le'
  have e1' := qle (show (1 / 10 ^ 12 + 3179 / 10 ^ 18 : ℚ) ≤ EL 4 by kernel_fact)
  have e2' := qle (show (1 / 10 ^ 12 + 3068 / 10 ^ 18 : ℚ) ≤ EL 5 by kernel_fact)
  have e3' := qle (show (1 / 10 ^ 12 + 2346 / 10 ^ 17 : ℚ) ≤ EL 6 by kernel_fact)
  have e4' := qle (show (1 / 10 ^ 12 + 2451 / 10 ^ 17 : ℚ) ≤ EL 7 by kernel_fact)
  push_cast at e1' e2' e3' e4'
  obtain ⟨hU, hZ', hA, hB⟩ := inputs_L h7 hC dist_u dist_z dist_a dist_b
    (by rw [μG]; push_cast; linarith) (by rw [μG]; push_cast; linarith)
    (by rw [μG]; push_cast; linarith) (by rw [μG]; push_cast; linarith)
  have hDdev := Bd_Ddev h0 hq7 hU hZ' hA hB
  have hDval : ∀ θ φ, WEll1Z2.eval ((gcFlow (1 / 256)).Dof u z) θ (psi φ) =
      (gcDr (1 / 256) (Rof u θ φ) (Zof z θ φ) (cos (2 * φ)) (sin (2 * φ)) : ℂ) := by
    intro θ φ
    have hvD : PolyExprS.Valid aRes (gcD (1 / 256)) :=
      (gcFlow_valid (1 / 256) aRes hE).1.1
    have hxB : FlowFieldS.Dof (gcFlow (1 / 256)) u z =
        PolyExprS.eval (xK KamTorusA.iota u z) (gcD (1 / 256)) :=
      eval_congr_noWS (fun i hi => by fin_cases i <;> simp_all [xB, xK]) _ hn.1
    rw [hxB, ← PolyExprS.evalAlg_apply,
      PolyExprS.eval_algHom (PolyExprS.evalAlg θ (KamTorusA.psi φ)) (continuous_evalAlg _ _) hx
        hvD]
    simp only [PolyExprS.evalAlg_apply]
    rw [eval_xK_real hu hz hur hzr, eval_gc_noW hn.1, hD]
  refine ⟨Rof u, Zof z, contDiff_Rof hu, contDiff_Zof hz, fun θ φ => ?_, fun θ φ => ?_,
    fun θ φ => ?_, fun θ φ => ?_, fun θ φ => ?_, fun θ φ => ?_, fun θ φ => ?_, fun θ φ => ?_,
    fun θ φ => ?_, fun θ φ => ?_, fun θ φ => ?_, fun θ φ => ?_⟩
  · simp only [Rof, eval_periodic_θ]
  · simp only [Zof, eval_periodic_θ]
  · simp only [Rof, psi_add_pi, eval_periodic_ψ]
  · simp only [Zof, psi_add_pi, eval_periodic_ψ]
  · have h := congrArg (fun x => WEll1Z2.eval x θ (KamTorusA.psi φ)) hR
    simp only [FlowFieldS.resR, eval_zero'] at h
    rw [← PolyExprS.evalAlg_apply,
      PolyExprS.eval_algHom (PolyExprS.evalAlg θ (KamTorusA.psi φ)) (continuous_evalAlg _ _) hx
        hv.1] at h
    simp only [PolyExprS.evalAlg_apply] at h
    rw [eval_xK_real hu hz hur hzr] at h
    simp only [FlowFieldS.resRp, gcFlow, PolyExprS.eval] at h
    rw [eval_gc_noW hn.1, eval_gc_noW hn.2.1, hD, hNR] at h
    simp only [ptC, Matrix.cons_val] at h
    have h' : (gcDr (1 / 256) (Rof u θ φ) (Zof z θ φ) (cos (2 * φ)) (sin (2 * φ)) : ℂ) *
        ((deriv (fun φ' => Rof u θ φ') φ + iota * deriv (fun θ' => Rof u θ' φ) θ : ℝ) : ℂ) =
        (gcNRr (1 / 256) (Rof u θ φ) (Zof z θ φ) (cos (2 * φ)) (sin (2 * φ)) : ℂ) := by
      linear_combination h
    exact_mod_cast h'
  · have h := congrArg (fun x => WEll1Z2.eval x θ (KamTorusA.psi φ)) hZ
    simp only [FlowFieldS.resZ, eval_zero'] at h
    rw [← PolyExprS.evalAlg_apply,
      PolyExprS.eval_algHom (PolyExprS.evalAlg θ (KamTorusA.psi φ)) (continuous_evalAlg _ _) hx
        hv.2] at h
    simp only [PolyExprS.evalAlg_apply] at h
    rw [eval_xK_real hu hz hur hzr] at h
    simp only [FlowFieldS.resZp, gcFlow, PolyExprS.eval] at h
    rw [eval_gc_noW hn.1, eval_gc_noW hn.2.2, hD, hNZ] at h
    simp only [ptC, Matrix.cons_val] at h
    have h' : (gcDr (1 / 256) (Rof u θ φ) (Zof z θ φ) (cos (2 * φ)) (sin (2 * φ)) : ℂ) *
        ((deriv (fun φ' => Zof z θ φ') φ + iota * deriv (fun θ' => Zof z θ' φ) θ : ℝ) : ℂ) =
        (gcNZr (1 / 256) (Rof u θ φ) (Zof z θ φ) (cos (2 * φ)) (sin (2 * φ)) : ℂ) := by
      linear_combination h
    exact_mod_cast h'
  · have h1 := KamNewton.norm_eval_le_of_Bd h0 hDdev θ (psi φ)
    rw [eval_sub', hDval, PlasmaLean.Theory.KAM.eval_algebraMap] at h1
    have h2 := (Complex.abs_re_le_norm _).trans h1
    simp only [Complex.sub_re, Complex.ofReal_re] at h2
    have hd := d0G_bounds.1
    have := (abs_le.mp h2).1
    norm_num at this ⊢
    linarith
  · obtain ⟨hq, -⟩ := eval_eV_ptC (hpt θ φ) hE (hu4 θ φ)
    rwa [e1] at hq
  · have h1 := abs_re_sub_le h0 hC.du θ (psi φ)
    simp only [Rof]
    rw [show 1 + (WEll1Z2.eval u θ (psi φ)).re - (1 + (WEll1Z2.eval u₀G θ (psi φ)).re) =
      (WEll1Z2.eval u θ (psi φ)).re - (WEll1Z2.eval u₀G θ (psi φ)).re by ring]
    exact h1
  · exact abs_re_sub_le h0 hC.dz θ (psi φ)
  · rw [(hasDerivAt_Rof_θ hu θ φ).deriv]
    exact abs_re_sub_le h0 hC.dut θ (psi φ)
  · rw [(hasDerivAt_Zof_θ hz θ φ).deriv]
    exact abs_re_sub_le h0 hC.dzt θ (psi φ)

/-! ## The exact torus is a flow torus of `gcField (1/256)` -/

/-- Bounds of the certified torus `K₀`: `|R₀ − 1| ≤ 0.1929`, `|z₀| ≤ 0.1622`,
`|∂_θ R₀| ≤ 0.1634`, `|∂_θ z₀| ≤ 0.1616`. -/
theorem K₀G_bounds (θ φ : ℝ) :
    |Rof u₀G θ φ - 1| ≤ 1929 / 10000 ∧ |Zof z₀G θ φ| ≤ 811 / 5000 ∧
      |(WEll1Z2.eval (dTh u₀G) θ (psi φ)).re| ≤ 817 / 5000 ∧
      |(WEll1Z2.eval (dTh z₀G) θ (psi φ)).re| ≤ 101 / 625 :=
  ⟨abs_Rof_sub_one_le rA_nonneg' Bd_u₀G θ φ, abs_Zof_le rA_nonneg' Bd_z₀G θ φ,
    (Complex.abs_re_le_norm _).trans (KamNewton.norm_eval_le_of_Bd rA_nonneg' Bd_dTh_u₀G θ _),
    (Complex.abs_re_le_norm _).trans (KamNewton.norm_eval_le_of_Bd rA_nonneg' Bd_dTh_z₀G θ _)⟩

/-- **The exact guiding-centre torus is a flow torus of `gcField (1/256)`** with rotational
transform `ι = (75 + √5)/562` and `0.03 ≤ rt ≤ 0.253`. -/
theorem gc_flowTorus :
    ∃ Rk zk : ℝ → ℝ → ℝ, FlowTorus (gcField (1 / 256)) iota (3 / 100) (253 / 1000) Rk zk := by
  obtain ⟨Rk, zk, hR2, hz2, p1, p2, p3, p4, iR, iZ, hD, hq, cR0, cZ0, cRθ, cZθ⟩ :=
    gc_exact_torus_data
  have hμ : μG = 1 / 10 ^ 12 := rfl
  -- pointwise estimates
  have ha : ∀ θ φ, |(Rk θ φ - 1) - (Rof u₀G θ φ - 1)| ≤ μG := fun θ φ => by
    rw [show Rk θ φ - 1 - (Rof u₀G θ φ - 1) = Rk θ φ - Rof u₀G θ φ by ring]; exact cR0 θ φ
  have hRpos : ∀ θ φ, 0 < Rk θ φ := fun θ φ => by
    have h1 := abs_le.mp (ha θ φ)
    have h2 := abs_le.mp (K₀G_bounds θ φ).1
    rw [hμ] at h1; linarith [h1.1, h2.1]
  have hrad : ∀ θ φ, 7 / 200 - 2 * μG ≤ (Rk θ φ - 1) * cos θ + zk θ φ * sin θ := fun θ φ => by
    have h0 := gc_radial_ge θ φ
    have h1 : |(Rk θ φ - Rof u₀G θ φ) * cos θ| ≤ μG := by
      rw [abs_mul]
      calc |Rk θ φ - Rof u₀G θ φ| * |cos θ| ≤ μG * 1 :=
            mul_le_mul (cR0 θ φ) (abs_cos_le_one θ) (abs_nonneg _) (by rw [hμ]; positivity)
        _ = μG := by ring
    have h2 : |(zk θ φ - Zof z₀G θ φ) * sin θ| ≤ μG := by
      rw [abs_mul]
      calc |zk θ φ - Zof z₀G θ φ| * |sin θ| ≤ μG * 1 :=
            mul_le_mul (cZ0 θ φ) (abs_sin_le_one θ) (abs_nonneg _) (by rw [hμ]; positivity)
        _ = μG := by ring
    have e : (Rk θ φ - 1) * cos θ + zk θ φ * sin θ = radG θ φ +
        (Rk θ φ - Rof u₀G θ φ) * cos θ + (zk θ φ - Zof z₀G θ φ) * sin θ := by
      rw [radG]; ring
    rw [e]
    linarith [(abs_le.mp h1).1, (abs_le.mp h2).1]
  have hrt_ge : ∀ θ φ, 3 / 100 ≤ rtK Rk zk θ φ := fun θ φ => by
    have h1 := hrad θ φ
    have hcs := cos_sq_add_sin_sq θ
    have hcsq : ((Rk θ φ - 1) * cos θ + zk θ φ * sin θ) ^ 2 ≤ (Rk θ φ - 1) ^ 2 + zk θ φ ^ 2 := by
      nlinarith [sq_nonneg ((Rk θ φ - 1) * sin θ - zk θ φ * cos θ)]
    rw [rtK, Real.le_sqrt (by norm_num) (by positivity)]
    rw [hμ] at h1
    nlinarith
  have hrt_le : ∀ θ φ, rtK Rk zk θ φ ≤ 253 / 1000 := fun θ φ => by
    have h1 := abs_le.mp (ha θ φ)
    have h2 := abs_le.mp (K₀G_bounds θ φ).1
    have h3 := abs_le.mp (cZ0 θ φ)
    have h4 := abs_le.mp (K₀G_bounds θ φ).2.1
    rw [hμ] at h1 h3
    rw [rtK, Real.sqrt_le_left (by norm_num)]
    nlinarith
  have hwind : ∀ θ φ, 0 < windK Rk zk θ φ := fun θ φ => by
    have hw := gc_winding_ge θ φ
    obtain ⟨b1, b2, b3, b4⟩ := K₀G_bounds θ φ
    have h1 := abs_mul_sub_mul_le (ha θ φ) (cZθ θ φ) b1 b4
    have h2 := abs_mul_sub_mul_le (cZ0 θ φ) (cRθ θ φ) b2 b3
    rw [windK]
    rw [windG] at hw
    have a1 := (abs_le.mp h1).1
    have a2 := (abs_le.mp h2).2
    rw [hμ] at a1 a2
    nlinarith
  refine ⟨Rk, zk, hR2, hz2, p1, p2, p3, p4, fun θ φ => ?_, fun θ φ => ?_, fun θ φ => ?_,
    fun θ φ => ?_, hwind, hrt_ge, hrt_le, by norm_num, by norm_num⟩
  · obtain ⟨h1, h2, -⟩ := cRTZ_gcField (1 / 256) (hRpos θ φ) φ (zk θ φ) (hq θ φ)
    rw [h1, h2, ← iR θ φ]
    ring
  · obtain ⟨-, h2, h3⟩ := cRTZ_gcField (1 / 256) (hRpos θ φ) φ (zk θ φ) (hq θ φ)
    rw [h3, h2, ← iZ θ φ]
    ring
  · obtain ⟨-, h2, -⟩ := cRTZ_gcField (1 / 256) (hRpos θ φ) φ (zk θ φ) (hq θ φ)
    rw [h2]
    have := hD θ φ
    have := hRpos θ φ
    positivity
  · have := hrad θ φ
    rw [hμ] at this
    linarith

/-! ## All-time confinement of the field lines of `gcField (1/256)` -/

/-- **All-time confinement of the field lines of the guiding-centre field** (`ρ_s = 1/256`, model
units `R₀ = B₀ = 1`). There is a torus profile `ρ` with `0.03 ≤ ρ ≤ 0.253` (the radial graph,
about the exact magnetic axis `R = 1, z = 0`, of the exact KAM torus of rotational transform
`(75 + √5)/562` of the guiding-centre field) such that

* from every point `x₀` on the axis or strictly inside the torus `rt < ρ(θs, φs)` there is
  **exactly one** two-sided field line `γ : ℝ → Space` of `gcField (1/256)` with `γ 0 = x₀`
  (it exists for all time); and
* every two-sided field line of `gcField (1/256)` starting on the axis or inside the torus stays
  inside it — in particular within distance `0.253` of the axis — for all time. -/
theorem rationalStellarator_gc_field_confined_forever :
    ∃ ρ : ℝ → ℝ → ℝ, TorusProfile ρ ∧ (∀ a b, 3 / 100 ≤ ρ a b) ∧ (∀ a b, ρ a b ≤ 253 / 1000) ∧
      (∀ x₀ : Space, (rt x₀ = 0 ∨ rt x₀ < ρ (θs x₀) (φs x₀)) →
        ∃! γ : ℝ → Space, IsFieldLine (gcField (1 / 256)) γ ∧ γ 0 = x₀) ∧
      ∀ γ : ℝ → Space, IsFieldLine (gcField (1 / 256)) γ →
        (rt (γ 0) = 0 ∨ rt (γ 0) < ρ (θs (γ 0)) (φs (γ 0))) →
        ∀ t, rt (γ t) ≤ 253 / 1000 ∧ (rt (γ t) = 0 ∨ rt (γ t) < ρ (θs (γ t)) (φs (γ t))) := by
  obtain ⟨Rk, zk, hK⟩ := gc_flowTorus
  obtain ⟨h1, h2⟩ := hK.confined_existsUnique isOpen_gcRegion (gcField_contDiffOn_one (1 / 256))
    (R₁ := 263 / 1000) (g₀ := 1 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun y hy => tube_subset_gcRegion (by linarith))
  exact ⟨hK.profile, hK.torusProfile, fun a b => (hK.profile_bounds a b).1,
    fun a b => (hK.profile_bounds a b).2, h1, h2⟩

end PlasmaLean.Design.RationalStellaratorGC
